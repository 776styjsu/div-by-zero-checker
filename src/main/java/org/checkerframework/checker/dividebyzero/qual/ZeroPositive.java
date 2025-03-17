package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

/**
 * The ZeroPositive type in the divide-by-zero type hierarchy.
 * This type is a subtype of Top.
 * It is used to represent values that are known to be greater than or
 * equal to zero.
 */
@SubtypeOf({Top.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface ZeroPositive {}