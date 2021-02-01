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
        // TODO
        // ASsuming that this returns true
        // then the
        // three cases: if it is less than zero or possibly zero
        // well, possibly zero is complicated... 
        // TODO write your own cases
        
        // will glb be helpful?
/*
        switch (operator){
            case EQ: // glb with the rhs determined?
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
        }*/

        return lhs;
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
        /*
        switch (operator) {
            case PLUS:
                if (lhs == positive() && rhs == positive()) {
                    return positive();
                } else if (lhs == negative() && rhs == negative()) {
                    return negative();
                } else if (lhs == zero() && rhs == zero()) {
                    return zero(); // TODO I don't think this case is necessary b/c of below
                } else if (lhs == zero()) {
                    return rhs; // could be anything
                } else if (rhs == zero()) {
                    return lhs;
                } else if (lhs == divbyzero() || rhs == divbyzero()) {
                    return divbyzero();
                } else { // e,g. NotZero plus either Pos, Neg, or NotZero
                    return maybezero(); // TODO are there no more cases?
                }
            case MINUS:
                if (lhs == positive() && rhs == negative()) {
                    return positive();
                } else if (lhs == negative() && rhs == positive()) {
                    return negative();
                } else if (lhs == zero() && rhs == zero()) {
                    return zero();
                } else if (lhs == zero()) {
                    if (rhs == positive()) {
                        return negative();
                    } else if (rhs == negative()) {
                        return positive();
                    } else return rhs;
                } else if (rhs == zero()) {
                    return lhs;
                } else if (lhs == divbyzero() || rhs == divbyzero()) {
                    return divbyzero();
                } else {
                    return maybezero(); // TODO are there no more cases?
                }
            case TIMES:
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
                } else if (lhs == divbyzero() || rhs == divbyzero()) {
                    return divbyzero();
                } else return notzero();
            case MOD:
    // TODO I do not know the right way to calculate the result of mod with negatives...
                if (lhs == positive() && rhs == positive()) {
                    return positive();
                } else if (lhs == negative() || rhs == negative()
                            || lhs == notzero() || rhs == notzero()) {
                    return notzero();
                } else if (rhs == zero ()|| rhs == maybezero()) {
                    return divbyzero();
                } else if (lhs == zero()) {
                    return zero();
                } else if (lhs == maybezero()) {
                    return maybezero();
                } else return top();
            case DIVIDE:
                if (rhs == zero() || lhs == maybezero()) {
                    return divbyzero(); // TODO ultimately not sure I see a use for MaybeZero
                } else if (lhs == zero()) {
                    return zero();
                } else if (lhs == maybezero()) {
                    return maybezero();
                } else if (lhs == positive() && rhs == positive()) {
                    return positive();
                } else if (lhs == positive() && rhs == negative() 
                            || rhs == positive() && lhs == negative()) {
                    return negative();
                } else if ((lhs == positive() || lhs == negative()) &&
                            (rhs == lhs)) {
                    return positive();
                } else if (lhs == notzero() || rhs == notzero()) {
                    return notzero();
                } else return top();
            }
*/
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
/*
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

    private AnnotationMirror divbyzero() {
        return reflect(DivByZero.class);
    }*/

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
