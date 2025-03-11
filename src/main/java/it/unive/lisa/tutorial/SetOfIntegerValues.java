package it.unive.lisa.tutorial;

import java.util.HashSet;
import java.util.Set;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class SetOfIntegerValues implements BaseNonRelationalValueDomain<SetOfIntegerValues>  {
    public static final SetOfIntegerValues BOTTOM = new SetOfIntegerValues(new HashSet<>()),TOP = new SetOfIntegerValues(null);
    public final Set<Integer> values;
    private static final int MAX_NUMBER_OF_ELEMENTS = 500;
    public SetOfIntegerValues(Set<Integer> values) {
        this.values = values;
    }
    public SetOfIntegerValues(int value) {
        this.values = new HashSet<>();
        this.values.add(value);
    }
    @Override
    public SetOfIntegerValues lubAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        HashSet<Integer> newValues = new HashSet<>(this.values);
        newValues.addAll(setOfIntegerValues.values);
        if(newValues.size() > MAX_NUMBER_OF_ELEMENTS)
            return top();
        return new SetOfIntegerValues(newValues);
    }

    @Override
    public boolean lessOrEqualAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        return setOfIntegerValues.values.containsAll(this.values);
    }

    @Override
    public SetOfIntegerValues top() {
        return TOP;
    }

    @Override
    public SetOfIntegerValues bottom() {
        return BOTTOM;
    }
    @Override
    public SetOfIntegerValues evalBinaryExpression(BinaryOperator operator, SetOfIntegerValues left, SetOfIntegerValues right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof AdditionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            Set<Integer> values = new HashSet<>();
            for(int leftValue : left.values)
                for(int rightValue : right.values)
                    values.add(leftValue + rightValue);
            return new SetOfIntegerValues(values);
        }
       
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }
     @Override
    public SetOfIntegerValues evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Integer)
            return new SetOfIntegerValues((Integer) constant.getValue());
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }
    @Override
    public StructuredRepresentation representation() {
        if(this.isBottom())
            return Lattice.bottomRepresentation();
        if(this.isTop())
            return Lattice.topRepresentation();
        return new StringRepresentation(values.toString());
    }

    public Satisfiability satisfiesBinaryExpression(BinaryOperator operator, SetOfIntegerValues left, SetOfIntegerValues right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(left.isTop() || right.isTop())
            return Satisfiability.UNKNOWN;
        if(operator instanceof ComparisonLt) {
            for(int leftValue : left.values)
                for(int rightValue : right.values)
                    if(leftValue < rightValue)
                        return Satisfiability.SATISFIED;
            return Satisfiability.NOT_SATISFIED;
        }
        return BaseNonRelationalValueDomain.super.satisfiesBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public ValueEnvironment<SetOfIntegerValues> assumeBinaryExpression(ValueEnvironment<SetOfIntegerValues> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle) throws SemanticException {

        if(operator instanceof ComparisonLt){
            if(left instanceof Variable && right instanceof Constant){
                Variable x = (Variable) left;
                Constant y = (Constant) right;
                if(y.getValue() instanceof Integer){
                    SetOfIntegerValues vals = environment.getState(x);
                    if(vals.isTop())
                        return environment;
                    HashSet<Integer> newValues = new HashSet<>();
                    for(int val : vals.values)
                        if(val < (int) y.getValue())
                            newValues.add(val);
                    environment.putState(x, new SetOfIntegerValues(newValues));
                    return environment;   
                }
            }
        }
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }
}