package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

import org.checkerframework.checker.dividebyzero.qual.Negative;
import org.checkerframework.checker.dividebyzero.qual.Zero;
import org.checkerframework.checker.dividebyzero.qual.Positive;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * The bottom type in the divide-by-zero type hierarchy.
 * This type is a subtype of all other types in the hierarchy.
 * It is used to represent values that are known to be invalid,
 * such as the result of dividing by zero.
 */
@SubtypeOf({Negative.class, Zero.class, Positive.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface Bottom {}
