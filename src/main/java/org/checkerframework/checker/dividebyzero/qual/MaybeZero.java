package org.checkerframework.checker.dividebyzero.qual;

import org.checkerframework.framework.qual.SubtypeOf;
import java.lang.annotation.Target;
import java.lang.annotation.ElementType;

@SubtypeOf(Top.class)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface MaybeZero {}

// TODO I have a real desire to remove this and turn it into Zero
// I feel like this is slightly more expressive (but unnecessarily complex)