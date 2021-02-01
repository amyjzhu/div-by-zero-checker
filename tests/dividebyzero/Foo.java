import org.checkerframework.checker.dividebyzero.qual.*;

// A simple test case for your divide-by-zero checker.
// The file contains "// ::" comments to indicate expected
// errors and warnings; see
// https://github.com/typetools/checker-framework/blob/master/checker/tests/README.
//
// Passing this test does not guarantee a perfect grade on this assignment,
// but it is an important start. You should always write your own test cases,
// in addition to using those provided to you.
class Foo {

    public static void f() {
        int one  = 1;
        int zero = 0;
        // :: error: divide.by.zero
        int x    = one / zero;
        int y    = zero / one;
        // :: error: divide.by.zero
        int z    = x / y;
        String s = "hello";
    }

    public static void g(int y) {
        if (y == 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        } else {
            int x = 1 / y;
        }

        if (y != 0) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y == 0)) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y != 0)) {
            // :: error: divide.by.zero
            int x = 1 / y;
        } else {
            int x = 1 / y;
        }

        if (y < 0) {
            int x = 1 / y;
        }

        if (y <= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (y > 0) {
            int x = 1 / y;
        }

        if (y >= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }
    }

    public static void h() {
        int zero_the_hard_way = 0 + 0 - 0 * 0;
        // :: error: divide.by.zero
        int x = 1 / zero_the_hard_way;

        int one_the_hard_way = 0 * 1 + 1;
        int y = 1 / one_the_hard_way;
    }

    public static void l() {
        // :: error: divide.by.zero
        int a = 1 / (1 - 1);
        int y = 1;
        // :: error: divide.by.zero
        int x = 1 / (y - y);
        int z = y-y;
        // :: error: divide.by.zero
        int k = 1/z;
    }

    public static void safeAddition() {
        // both positive
        int a = 1 / (2 + 3);

        // both negative
        int b = -1 / (-4 + -6);
    }

    public static void safeSubtraction() {
        // negative minus a postive isn't zero
        int a = 1 / (-3 - 4);

        // positive minus a negative isn't zero
        int b = -5;
        int c = 10 / (1 - b);
    }

    public static void multiplicationPreservesSigns() {

        int a = 1 * 2;
        int b = 3 + a;
        int c = -1 / b;

        int d = 1 * -3;
        int e = 3 + d;
        // :: error: divide.by.zero
        int f = 2 / e;
    }

    public static void complicatedSafeSequence() {
        int c = 3;
        c += 5;
        c *= (2 + 1);
        c *= (-3 * -4);
        c += 1;
        int d = 1 / c;
    }

    public static void divisionAssignment() {
        int a = 3;
        // :: error: divide.by.zero
        a /= 0;

        int b = 10;
        // :: error: divide.by.zero
        b /= (3 * 0);
    }

    /// ====
    public static void plusZero() {
        int a = 4 - 0;
        int b = -3 + 0;

        int c = 1 / a;
        int d = 1 / b;
    }

    public static void zeroMinus() {
        // 0 minus notzero is notzero
        int a = -4 % -5;

        int b = 1 / (0 - a);

        // zero minus positive is negative
        int c = 1 / (0 - 4);
    }

    public static void divideZero() {
        int a = 4 - 3;

        // both are "maybe zero"
        int b = a / 5;
        int c = 0 / 5;

        // :: error: divide.by.zero
        int d = a / b;
        // :: error: divide.by.zero
        int e = c / b;
    }

    public static void nonsafeAddition() {
        // :: error: divide.by.zero
        int a = 1 / (2 + -3);

        // :: error: divide.by.zero
        int b = -1 / (-4 + 6);
    }

    public static void nonsafeSubtraction() {
        // :: error: divide.by.zero
        int a = 1 / (2 - 3);

        // this is okay 
        int b = -1 / (4 - -6);

        // :: error: divide.by.zero
        int c = -1 / (-4 - -6);
    }

    public static void negativeRemainder() {
        int a = -4;
        int b = 3;

        int c = a % b; // nonzero element
        int d = b % a;

        // this is fine, they're not zero
        int e = a / c;
        int f = b / d;

        int g = a + c;
        int h = b + d; // now it could be zero

        // :: error: divide.by.zero
        int i = b / g;

        // :: error: divide.by.zero
        int j = a / h;

        // but if we refine...
        if (g > 0) {
            int k = a / g;
            if (h < 0) {
                int l = b / h;
            }
        } else {
            // :: error: divide.by.zero
            int k = a / g;
            // :: error: divide.by.zero
            int l = b / h;
        }

        // also, mod of a nonzero is nonzero
        int m = c % d;
        int n = 4 / m;
    }

    public static void modZero() {
        int a = 0 % 5;

        // :: error: divide.by.zero 
        int b = 1 / a;
    }

}
