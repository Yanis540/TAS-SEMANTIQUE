package it.unive.lisa.tutorial;

import java.util.HashSet;
import java.util.Set;

import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;

public class ExtendedSignsAndLinearInequalityCartesian extends CartesianProduct<ExtendedSignsAndLinearInequalityCartesian,TwoVariablesInequality,ValueEnvironment<ExtendedSigns>,ValueExpression,Identifier>
implements ValueDomain<ExtendedSignsAndLinearInequalityCartesian>
{
    public ExtendedSignsAndLinearInequalityCartesian(TwoVariablesInequality left, ValueEnvironment<ExtendedSigns> right) {
        super(left, right);
    }
    @Override
    public boolean knowsIdentifier(Identifier id) {
        return left.knowsIdentifier(id) || right.knowsIdentifier(id);
    }

    @Override
    public ExtendedSignsAndLinearInequalityCartesian mk(TwoVariablesInequality left, ValueEnvironment<ExtendedSigns> right) {
        return new ExtendedSignsAndLinearInequalityCartesian(left, right);
    }
    
}
