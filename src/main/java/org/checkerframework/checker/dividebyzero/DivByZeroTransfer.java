package org.checkerframework.checker.dividebyzero;

import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;

import java.util.Set;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroTransfer extends CFTransfer {

    enum Comparison {
        /** == */ EQ,
        /** != */ NE,
        /** <  */ LT,
        /** <= */ LE,
        /** >  */ GT,
        /** >= */ GE
    }

    enum BinaryOperator {
        /** + */ PLUS,
        /** - */ MINUS,
        /** * */ TIMES,
        /** / */ DIVIDE,
        /** % */ MOD
    }

    // ========================================================================
    // Transfer functions to implement

    /**
     * Assuming that a simple comparison (lhs `op` rhs) returns true, this
     * function should refine what we know about the left-hand side (lhs). (The
     * input value "lhs" is always a legal return value, but not a very useful
     * one.)
     *
     * <p>For example, given the code
     * <pre>
     * if (y != 0) { x = 1 / y; }
     * </pre>
     * the comparison "y != 0" causes us to learn the fact that "y is not zero"
     * inside the body of the if-statement. This function would be called with
     * "NE", "top", and "zero", and should return "not zero" (or the appropriate
     * result for your lattice).
     *
     * <p>Note that the returned value should always be lower in the lattice
     * than the given point for lhs. The "glb" helper function below will
     * probably be useful here.
     *
     * @param operator   a comparison operator
     * @param lhs        the lattice point for the left-hand side of the comparison expression
     * @param rhs        the lattice point for the right-hand side of the comparison expression
     * @return a refined type for lhs
     */
    private AnnotationMirror refineLhsOfComparison(
            Comparison operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        switch (operator){
            case EQ: 
                return glb(lhs, rhs);
            case NE:
                if (rhs.equals(zero())) {
                    return glb(lhs, notzero());
                } // what if it's a possibly zero? it's still the same...
                else if (rhs.equals(maybezero())) {
                    return glb(lhs, rhs);
                } else {
                    return lhs; // probably still the same
                }
            case LE:
                if (rhs.equals(negative())) return glb(lhs, negative());
                return glb(lhs, maybezero());
            case LT:
                if (rhs.equals(zero()) || rhs.equals(negative())) return glb(lhs, negative());
                return glb(lhs, maybezero());
            case GE:
                if (rhs.equals(positive())) return glb(lhs, positive());
                return glb(lhs, maybezero());
            case GT:
                if (rhs.equals(zero()) || rhs.equals(positive())) return glb(lhs, positive());
                return glb(lhs, maybezero());
        }

        return lhs;
    }

    /**
     * Return true if the two sides have the same annotation
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
    */
    private boolean sameAnnotation(AnnotationMirror lhs, AnnotationMirror rhs) {
        return lhs.equals(rhs);
    }

    /**
     * Return true if the two sides have both of the desired annotations
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @param desired1   lattice point should belong to exactly one of lhs or rhs
     * @param desired2   lattice point should belong to exactly one of lhs or rhs
    */
    private boolean bothOf(AnnotationMirror lhs, AnnotationMirror rhs, AnnotationMirror desired1, AnnotationMirror desired2) {
        return (lhs == desired1 && rhs == desired2) || (lhs == desired2 && rhs == desired1);
    }

    private AnnotationMirror plusTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
        // two positives or two negatives retains the sign
        if (lhs == positive() && rhs == positive()) {
            return positive();
        } else if (lhs == negative() && rhs == negative()) {
            return negative();
        // if either side is zero, there's no change
        } else if (lhs == zero()) {
            return rhs; 
        } else if (rhs == zero()) {
            return lhs;
        } else { 
            // Who knows? includes pos + neg cases, notzero cases, and maybezero cases
            return maybezero(); 
        }
    }

    private AnnotationMirror minusTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
        // if the sign stays the same, we have the same precision
        if (lhs == positive() && rhs == negative()) {
            return positive();
        } else if (lhs == negative() && rhs == positive()) {
            return negative();
        // x - 0 does nothing
        } else if (rhs == zero()) {
            return lhs;
        // if it's 0 - x we flip the sign for + and -
        } else if (lhs == zero()) {
            if (rhs == positive()) {
                return negative();
            } else if (rhs == negative()) {
                return positive();
            // 0 - maybezero is maybezero, 0 - notzero is notzero
            } else return rhs; 
        } else {
            return maybezero(); // TODO are there no more cases?
        }
    }

    private AnnotationMirror timesTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
        // if we know the sign we can determine precisely the lattice point
        if (lhs == positive() && rhs == negative() 
                || rhs == positive() && lhs == negative()) {
            return negative();
        } else if ((lhs == positive() || lhs == negative()) &&
                    (rhs == lhs)) {
            return positive();
        } else if (lhs == zero() || rhs == zero()) {
            return zero();
        } else if (lhs == maybezero() || rhs == maybezero()) {
            return maybezero();
        } else return notzero();        
    }

    private AnnotationMirror modTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
        // I'm not sure what % with negatives should return. It seems language-dependent
        // Just going to roll with "Not zero" for now.
        // Essentially only a partial function because of the division by zero case (ret. top)
        if (lhs == positive() && rhs == positive()) {
            return positive();
        } else if (lhs == negative() || rhs == negative()
                    || lhs == notzero() || rhs == notzero()) {
            return notzero();
        // mod of 0 is always 0
        } else if (lhs == zero()) {
            return zero();
        } else if (lhs == maybezero()) {
            return maybezero();
        } else return top(); 
    }

    private AnnotationMirror divideTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
        // Essentially only a partial function because of the division by zero case (ret. top)
        if (lhs == zero() || lhs == maybezero()) {
            return lhs;
        // again, if we know the sign, we know it precisely
        } else if (lhs == positive() && rhs == positive()) {
            return positive();
        } else if (lhs == positive() && rhs == negative() 
                    || rhs == positive() && lhs == negative()) {
            return negative();
        } else if ((lhs == positive() || lhs == negative()) &&
                    (rhs == lhs)) {
            return positive();
        // otherwise, well, it's not zero
        } else if (lhs == notzero() || rhs == notzero()) {
            return notzero();
        } else return top();
    }

    /**
     * For an arithmetic expression (lhs `op` rhs), compute the point in the
     * lattice for the result of evaluating the expression. ("Top" is always a
     * legal return value, but not a very useful one.)
     *
     * <p>For example,
     * <pre>x = 1 + 0</pre>
     * should cause us to conclude that "x is not zero".
     *
     * @param operator   a binary operator
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @return the lattice point for the result of the expression
     */
    private AnnotationMirror arithmeticTransfer(
            BinaryOperator operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        // TODO refactor. maybe with functions like sameType or whatnot
        
        switch (operator) {
            case PLUS:
                return plusTransfer(lhs, rhs);
            case MINUS:
                return minusTransfer(lhs, rhs);
            case TIMES:
                return timesTransfer(lhs, rhs);
            case MOD:
                return modTransfer(lhs, rhs);
            case DIVIDE:
                return divideTransfer(lhs, rhs);
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
        return analysis.getTypeFactory().getQualifierHierarchy().getBottomAnnotations().iterator().next();
    }

    /** Compute the least-upper-bound of two points in the lattice */
    private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBound(x, y);
    }

    /** Compute the greatest-lower-bound of two points in the lattice */
    private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBound(x, y);
    }

    private AnnotationMirror positive() {
        return reflect(Positive.class);
    }
    
    private AnnotationMirror negative() {
        return reflect(Negative.class);
    }
    
    private AnnotationMirror notzero() {
        return reflect(NotZero.class);
    }
    
    private AnnotationMirror maybezero() {
        return reflect(MaybeZero.class);
    }
    
    private AnnotationMirror zero() {
        return reflect(Zero.class);
    }

    /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
    private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
        return AnnotationBuilder.fromClass(
            analysis.getTypeFactory().getProcessingEnv().getElementUtils(),
            qualifier);
    }

    /** Determine whether two AnnotationMirrors are the same point in the lattice */
    private boolean equal(AnnotationMirror x, AnnotationMirror y) {
        return AnnotationUtils.areSame(x, y);
    }

    /** `x op y` == `y flip(op) x` */
    private Comparison flip(Comparison op) {
        switch (op) {
            case EQ: return Comparison.EQ;
            case NE: return Comparison.NE;
            case LT: return Comparison.GT;
            case LE: return Comparison.GE;
            case GT: return Comparison.LT;
            case GE: return Comparison.LE;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    /** `x op y` == `!(x negate(op) y)` */
    private Comparison negate(Comparison op) {
        switch (op) {
            case EQ: return Comparison.NE;
            case NE: return Comparison.EQ;
            case LT: return Comparison.GE;
            case LE: return Comparison.GT;
            case GT: return Comparison.LE;
            case GE: return Comparison.LT;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroTransfer(CFAnalysis analysis) {
        super(analysis);
    }

    private TransferResult<CFValue, CFStore> implementComparison(Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        CFStore thenStore = out.getThenStore().copy();
        CFStore elseStore = out.getElseStore().copy();

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(op, l, r));

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(op), r, l));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(negate(op), l, r));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(negate(op)), r, l));

        return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
    }

    private TransferResult<CFValue, CFStore> implementOperator(BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        AnnotationMirror res = arithmeticTransfer(op, l, r);
        CFValue newResultValue = analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
        return new RegularTransferResult<>(newResultValue, out.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(EqualToNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(NotEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(LessThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerDivision(IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerRemainder(IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingDivision(FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingRemainder(FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalMultiplication(NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalAddition(NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalSubtraction(NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
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
