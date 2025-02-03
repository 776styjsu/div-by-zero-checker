package org.checkerframework.checker.dividebyzero;

import java.lang.annotation.Annotation;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;
import java.util.Collections;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.AnnotationValue;

import org.checkerframework.checker.dividebyzero.qual.*;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

public class DivByZeroTransfer extends CFTransfer {

  enum Comparison {
    /** == */
    EQ,
    /** != */
    NE,
    /** < */
    LT,
    /** <= */
    LE,
    /** > */
    GT,
    /** >= */
    GE
  }

  enum BinaryOperator {
    /** + */
    PLUS,
    /** - */
    MINUS,
    /** * */
    TIMES,
    /** / */
    DIVIDE,
    /** % */
    MOD
  }

  // ========================================================================
  // Transfer functions to implement

  /**
   * Assuming that a simple comparison (lhs `op` rhs) returns true, this function
   * should refine what
   * we know about the left-hand side (lhs). (The input value "lhs" is always a
   * legal return value,
   * but not a very useful one.)
   *
   * <p>
   * For example, given the code
   *
   * <pre>
   * if (y != 0) {
   *   x = 1 / y;
   * }
   * </pre>
   *
   * the comparison "y != 0" causes us to learn the fact that "y is not zero"
   * inside the body of the
   * if-statement. This function would be called with "NE", "top", and "zero", and
   * should return
   * "not zero" (or the appropriate result for your lattice).
   *
   * <p>
   * Note that the returned value should always be lower in the lattice than the
   * given point for
   * lhs. The "glb" helper function below will probably be useful here.
   *
   * @param operator a comparison operator
   * @param lhs      the lattice point for the left-hand side of the comparison
   *                 expression
   * @param rhs      the lattice point for the right-hand side of the comparison
   *                 expression
   * @return a refined type for lhs
   */
  private AnnotationMirror refineLhsOfComparison(
      Comparison operator, AnnotationMirror lhs, AnnotationMirror rhs) {
    switch (operator) {
      case EQ:
        return glb(lhs, rhs);

      case NE:
        // If x != y holds then we know that x is not equal to y.
        // In the common case where y is 0 we can remove zero.
        if (equal(rhs, reflect(Zero.class))) {
          if (equal(lhs, reflect(ZeroPositive.class))) {
            return glb(lhs, reflect(Positive.class));
          } else if (equal(lhs, reflect(NegativeZero.class))) {
            return glb(lhs, reflect(Negative.class));
          } else {
            return reflect(NegativePositive.class);
          }
        }
        return lhs;

      case LT:
        // If x < y holds then we may be able to infer that x is “less than” some
        // constant.
        // For example, if y is 0 (or an imprecise nonnegative value), then x < 0 so x
        // must be negative.
        if (equal(rhs, reflect(Zero.class)) || equal(rhs, reflect(ZeroPositive.class))) {
          return glb(lhs, reflect(Negative.class));
        }
        // If y is Positive then x < Positive means that x could be negative or zero.
        // In our lattice, the best we can say is that x is in NegativeZero.
        if (equal(rhs, reflect(Positive.class))) {
          return glb(lhs, reflect(NegativeZero.class));
        }
        return lhs;

      case LE:
        // If x <= y holds then for instance, if y is 0 (or imprecise nonnegative),
        // x must be less than or equal to 0, i.e. x is in NegativeZero.
        if (equal(rhs, reflect(Zero.class)) || equal(rhs, reflect(ZeroPositive.class))) {
          return glb(lhs, reflect(NegativeZero.class));
        }
        // If y is Positive then x <= Positive means that x is either zero or positive.
        // Thus, we refine x with ZeroPositive.
        if (equal(rhs, reflect(Positive.class))) {
          return glb(lhs, reflect(ZeroPositive.class));
        }
        return lhs;

      case GT:
        // If x > y holds then if y is 0 (or an imprecise nonpositive value) we know x >
        // 0.
        if (equal(rhs, reflect(Zero.class)) || equal(rhs, reflect(NegativeZero.class))) {
          return glb(lhs, reflect(Positive.class));
        }
        // If y is Negative then x > Negative means that x is zero or positive.
        // In our lattice that information is captured by ZeroPositive.
        if (equal(rhs, reflect(Negative.class))) {
          return glb(lhs, reflect(ZeroPositive.class));
        }
        return lhs;

      case GE:
        // If x >= y holds then if y is 0 (or imprecise nonpositive) then x is zero or
        // positive.
        if (equal(rhs, reflect(Zero.class)) || equal(rhs, reflect(NegativeZero.class))) {
          return glb(lhs, reflect(ZeroPositive.class));
        }
        // If y is Positive then x >= Positive forces x to be positive.
        if (equal(rhs, reflect(Positive.class))) {
          return glb(lhs, reflect(Positive.class));
        }
        return lhs;

      default:
        return lhs;
    }
  }

  /**
   * For an arithmetic expression (lhs `op` rhs), compute the point in the lattice
   * for the result of
   * evaluating the expression. ("Top" is always a legal return value, but not a
   * very useful one.)
   *
   * <p>
   * For example,
   *
   * <pre>
   * x = 1 + 0
   * </pre>
   *
   * should cause us to conclude that "x is not zero".
   *
   * @param operator a binary operator
   * @param lhs      the lattice point for the left-hand side of the expression
   * @param rhs      the lattice point for the right-hand side of the expression
   * @return the lattice point for the result of the expression
   */
  private AnnotationMirror arithmeticTransfer(
      BinaryOperator operator, AnnotationMirror lhs, AnnotationMirror rhs) {
    switch (operator) {
      case PLUS:
        if (equal(lhs, reflect(Zero.class))) {
          return rhs; // Zero + X => X
        }
        if (equal(rhs, reflect(Zero.class))) {
          return lhs; // X + Zero => X
        }

        if (equal(lhs, rhs)) {
          return lhs;
        }

        // Non-negative + positive = positive.
        if ((equal(lhs, reflect(Positive.class)) || equal(rhs, reflect(Positive.class)))
            && (equal(lhs, reflect(ZeroPositive.class)) || equal(rhs, reflect(ZeroPositive.class)))) {
          return reflect(Positive.class);
        }

        // Non-positive + negative = negative.
        if ((equal(lhs, reflect(Negative.class)) || equal(rhs, reflect(Negative.class)))
            && (equal(lhs, reflect(NegativeZero.class)) || equal(rhs, reflect(NegativeZero.class)))) {
          return reflect(Negative.class);
        }

        // Default case.
        return top();

      case MINUS:
        // Map for unary negation.
        Map<AnnotationMirror, AnnotationMirror> negationMap = Map.of(
            reflect(Positive.class), reflect(Negative.class),
            reflect(Negative.class), reflect(Positive.class),
            reflect(ZeroPositive.class), reflect(NegativeZero.class),
            reflect(NegativeZero.class), reflect(ZeroPositive.class));

        // If lhs and rhs are equal, we don't know the sign of the result.
        if (equal(lhs, rhs)) {
          return reflect(Top.class);
        }

        // If lhs is Zero, return the negation of rhs.
        if (equal(lhs, reflect(Zero.class))) {
          return negationMap.getOrDefault(rhs, rhs);
        }

        // If rhs is Zero, return lhs
        if (equal(rhs, reflect(Zero.class))) {
          return lhs;
        }

        // Extended negation map for imprecise annotations.
        Map<AnnotationMirror, Set<AnnotationMirror>> extendedNegationMap = Map.of(
            reflect(Positive.class), Set.of(reflect(Negative.class), reflect(NegativeZero.class)),
            reflect(Negative.class), Set.of(reflect(Positive.class), reflect(ZeroPositive.class)));

        // If rhs is negation of lhs, return lhs
        if (extendedNegationMap.containsKey(lhs) && extendedNegationMap.get(lhs).contains(rhs)) {
          return lhs;
        }

        // Special cases for imprecise lhs:
        // Non-negative - negative = positive and non-positive - positive = negative.
        if (equal(lhs, reflect(ZeroPositive.class)) && equal(rhs, reflect(Negative.class))) {
          return reflect(Positive.class);
        }
        if (equal(lhs, reflect(NegativeZero.class)) && equal(rhs, reflect(Positive.class))) {
          return reflect(Negative.class);
        }

        return top();

      case TIMES:
        // Multiplication is commutative so we simply combine the possible signs.
        Set<Integer> lhsSigns = getPossibleSigns(lhs);
        Set<Integer> rhsSigns = getPossibleSigns(rhs);
        Set<Integer> productSigns = new HashSet<>();
        for (int s1 : lhsSigns) {
          for (int s2 : rhsSigns) {
            productSigns.add(s1 * s2);
          }
        }

        return signSetToAnnotation(productSigns);

      case DIVIDE:
        // If the divisor might be zero, return bottom (unsafe division).
        if (isPotentialZero(rhs)) {
          return bottom();
        }

        // 0 / x = 0
        if (equal(lhs, reflect(Zero.class))) {
          return reflect(Zero.class);
        }

        // Compute the possible sign sets for numerator and denominator.
        lhsSigns = getPossibleSigns(lhs);
        rhsSigns = getPossibleSigns(rhs);

        // Compute the set of result signs.
        Set<Integer> resultSigns = new HashSet<>();
        for (int l : lhsSigns) {
          for (int r : rhsSigns) {
            resultSigns.add(l * r);
          }
        }

        return signSetToAnnotation(resultSigns);

      case MOD:
        // If the divisor might be zero, return bottom (unsafe division).
        if (isPotentialZero(rhs)) {
          return bottom();
        }

        // 0 % x = 0
        if (equal(lhs, reflect(Zero.class))) {
          return reflect(Zero.class);
        }

        // Compute the possible sign sets for numerator and denominator.
        if (equal(lhs, reflect(Positive.class))) {
          return reflect(ZeroPositive.class);
        }
        if (equal(lhs, reflect(Negative.class))) {
          return reflect(NegativeZero.class);
        }

        // For imprecise dividends, simply propagate the dividend's imprecision.
        if (equal(lhs, reflect(ZeroPositive.class)) || equal(lhs, reflect(NegativeZero.class))) {
          return lhs;
        }

        // Default case.
        return top();
    }

    return top();
  }

  // Helper: check whether an annotation might be zero.
  private boolean isPotentialZero(AnnotationMirror ann) {
    return equal(ann, reflect(Zero.class))
        || equal(ann, reflect(NegativeZero.class))
        || equal(ann, reflect(ZeroPositive.class))
        || equal(ann, top());
  }

  // Helper: return the set of possible signs.
  // We use -1 for negative, 0 for zero, and 1 for positive.
  private Set<Integer> getPossibleSigns(AnnotationMirror ann) {
    if (equal(ann, reflect(Zero.class))) {
      return Collections.singleton(0);
    } else if (equal(ann, reflect(Positive.class))) {
      return Collections.singleton(1);
    } else if (equal(ann, reflect(Negative.class))) {
      return Collections.singleton(-1);
    } else if (equal(ann, reflect(ZeroPositive.class))) {
      return new HashSet<>(Arrays.asList(0, 1));
    } else if (equal(ann, reflect(NegativeZero.class))) {
      return new HashSet<>(Arrays.asList(-1, 0));
    } else if (equal(ann, reflect(NegativePositive.class))) {
      return new HashSet<>(Arrays.asList(-1, 1));
    }
    // For top or any unknown annotation, assume all possibilities.
    return new HashSet<>(Arrays.asList(-1, 0, 1));
  }

  // Helper: map a set of possible signs to an annotation.
  private AnnotationMirror signSetToAnnotation(Set<Integer> signs) {
    if (signs.equals(Collections.singleton(1))) {
      return reflect(Positive.class);
    } else if (signs.equals(Collections.singleton(-1))) {
      return reflect(Negative.class);
    } else if (signs.equals(Collections.singleton(0))) {
      return reflect(Zero.class);
    } else if (signs.equals(new HashSet<>(Arrays.asList(0, 1)))) {
      return reflect(ZeroPositive.class);
    } else if (signs.equals(new HashSet<>(Arrays.asList(-1, 0)))) {
      return reflect(NegativeZero.class);
    }
    return top();
  }

  // ========================================================================
  // Useful helpers

  /** Get the top of the lattice */
  private AnnotationMirror top() {
    return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
  }

  /** Get the bottom of the lattice */
  private AnnotationMirror bottom() {
    return analysis
        .getTypeFactory()
        .getQualifierHierarchy()
        .getBottomAnnotations()
        .iterator()
        .next();
  }

  /** Compute the least-upper-bound of two points in the lattice */
  private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBoundQualifiersOnly(x, y);
  }

  /** Compute the greatest-lower-bound of two points in the lattice */
  private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBoundQualifiersOnly(x, y);
  }

  /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
  private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
    return AnnotationBuilder.fromClass(
        analysis.getTypeFactory().getProcessingEnv().getElementUtils(), qualifier);
  }

  /** Determine whether two AnnotationMirrors are the same point in the lattice */
  private boolean equal(AnnotationMirror x, AnnotationMirror y) {
    return AnnotationUtils.areSame(x, y);
  }

  /** `x op y` == `y flip(op) x` */
  private Comparison flip(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.EQ;
      case NE:
        return Comparison.NE;
      case LT:
        return Comparison.GT;
      case LE:
        return Comparison.GE;
      case GT:
        return Comparison.LT;
      case GE:
        return Comparison.LE;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  /** `x op y` == `!(x negate(op) y)` */
  private Comparison negate(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.NE;
      case NE:
        return Comparison.EQ;
      case LT:
        return Comparison.GE;
      case LE:
        return Comparison.GT;
      case GT:
        return Comparison.LE;
      case GE:
        return Comparison.LT;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  // ========================================================================
  // Checker Framework plumbing

  public DivByZeroTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  private TransferResult<CFValue, CFStore> implementComparison(
      Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l =
        findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r =
        findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    CFStore thenStore = out.getThenStore().copy();
    CFStore elseStore = out.getElseStore().copy();

    thenStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(op, l, r));

    thenStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()), refineLhsOfComparison(flip(op), r, l));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(negate(op), l, r));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()),
        refineLhsOfComparison(flip(negate(op)), r, l));

    return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
  }

  private TransferResult<CFValue, CFStore> implementOperator(
      BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    AnnotationMirror res = arithmeticTransfer(op, l, r);
    CFValue newResultValue =
        analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
    return new RegularTransferResult<>(newResultValue, out.getRegularStore());
  }

  @Override
  public TransferResult<CFValue, CFStore> visitEqualTo(
      EqualToNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNotEqual(
      NotEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThan(
      GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(
      GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThan(
      LessThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThanOrEqual(
      LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerDivision(
      IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerRemainder(
      IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingDivision(
      FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingRemainder(
      FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalMultiplication(
      NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalAddition(
      NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalSubtraction(
      NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
  }

  private static AnnotationMirror findAnnotation(
      Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
    if (set.size() == 0) {
      return null;
    }
    Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
    return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
  }
}
