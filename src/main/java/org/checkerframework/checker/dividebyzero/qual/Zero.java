package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

import org.checkerframework.checker.dividebyzero.qual.NegativeZero;
import org.checkerframework.checker.dividebyzero.qual.ZeroPositive;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * The Zero type in the divide-by-zero type hierarchy.
 * This type is a subtype of NegativeZero and ZeroPositive.
 * It is used to represent values that are known to be zero.
 */
@SubtypeOf({NegativeZero.class, ZeroPositive.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface Zero {}