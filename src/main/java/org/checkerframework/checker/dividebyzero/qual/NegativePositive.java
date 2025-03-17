package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * The NegativePositive type in the divide-by-zero type hierarchy.
 * This type is a subtype of Top.
 * It is used to represent values that is non-zero and can be either negative or
 * positive.
 */
@SubtypeOf({ Top.class })
@Target({ ElementType.TYPE_USE, ElementType.TYPE_PARAMETER })
public @interface NegativePositive {
}
