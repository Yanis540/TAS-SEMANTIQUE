package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.Environment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.program.cfg.statement.logic.Not;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.*;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.symbolic.value.operator.unary.LogicalNegation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

public class NotEqualsDomain extends FunctionalLattice<NotEqualsDomain, Identifier, NotEqualsDomain.SetOfIdentifiers> implements ValueDomain<NotEqualsDomain> {

    public NotEqualsDomain(SetOfIdentifiers lattice, Map<Identifier, SetOfIdentifiers> function) {
        super(lattice, function);
    }

    public NotEqualsDomain(SetOfIdentifiers lattice) {
        super(lattice);
    }

    public NotEqualsDomain() {
        super(new SetOfIdentifiers(Collections.emptySet(), true));
    }

    @Override
    public SetOfIdentifiers stateOfUnknown(Identifier identifier) {
        return new SetOfIdentifiers(Collections.emptySet(), true);
    }

    @Override
    public NotEqualsDomain mk(SetOfIdentifiers identifiers, Map<Identifier, SetOfIdentifiers> map) {
        return new NotEqualsDomain(identifiers, map);
    }

    @Override
    public NotEqualsDomain top() {
        return new NotEqualsDomain(lattice.top(), null);
    }

    @Override
    public NotEqualsDomain bottom() {
        return new NotEqualsDomain(lattice.bottom(), null);
    }

    @Override
    public NotEqualsDomain assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        NotEqualsDomain result = this.forgetIdentifier(identifier);
        if(valueExpression instanceof BinaryExpression) {
            BinaryExpression binaryExpression = (BinaryExpression) valueExpression;
            if(binaryExpression.getOperator() instanceof AdditionOperator || binaryExpression.getOperator() instanceof SubtractionOperator) {
                if(binaryExpression.getLeft() instanceof Identifier || binaryExpression.getRight() instanceof Constant) {
                    Identifier leftVariable = (Identifier) binaryExpression.getLeft();
                    Constant rightConstant = (Constant) binaryExpression.getRight();
                    if(rightConstant.getValue() instanceof Integer && ((Integer) rightConstant.getValue()).intValue() != 0) {
                        result = this.putState(identifier, new SetOfIdentifiers(Collections.singleton(leftVariable), false));
                    }
                }
            }
        }
        if(valueExpression instanceof Identifier) {
            result = result.putState(identifier, result.getState((Identifier) valueExpression));
        }
        return result.close();
    }

    private NotEqualsDomain close() {
        NotEqualsDomain result = this;
        for(Identifier domain : this.getKeys())
            for(Identifier codomain : this.getState(domain)) {
                Set<Identifier> value = new HashSet<>(result.getState(codomain).elements);
                value.add(domain);
                result = result.putState(codomain, new SetOfIdentifiers(value, false));
            }
        return result;
    }

    @Override
    public NotEqualsDomain smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return this;
    }

    @Override
    public NotEqualsDomain assume(ValueExpression valueExpression, ProgramPoint programPoint, ProgramPoint programPoint1, SemanticOracle semanticOracle) throws SemanticException {
        NotEqualsDomain result = this;
        if(valueExpression instanceof UnaryExpression && ((UnaryExpression) valueExpression).getOperator() instanceof LogicalNegation) {
            SymbolicExpression expression = ((UnaryExpression) valueExpression).getExpression();
            if(expression instanceof BinaryExpression) {
                BinaryExpression binaryExpression = (BinaryExpression) expression;
                if(binaryExpression.getOperator() instanceof ComparisonEq && binaryExpression.getLeft() instanceof Identifier && binaryExpression.getLeft() instanceof Variable && binaryExpression.getRight() instanceof Variable) {
                    Identifier leftVariable = (Identifier) binaryExpression.getLeft();
                    Identifier rightVariable = (Identifier) binaryExpression.getRight();
                    Set<Identifier> value = new HashSet<>(this.getState(leftVariable).elements);
                    value.add(rightVariable);
                    result = result.putState(leftVariable, new SetOfIdentifiers(value, false));
                    value = new HashSet<>(this.getState(rightVariable).elements);
                    value.add(leftVariable);
                    result = result.putState(rightVariable, new SetOfIdentifiers(value, false));
                }
            }
        }
        return result.close();
    }

    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return this.lattice.contains(identifier);
    }

    @Override
    public NotEqualsDomain forgetIdentifier(Identifier identifier) throws SemanticException {
        NotEqualsDomain result = this;
        if(result.getKeys().contains(identifier)) {
            result=result.putState(identifier, new SetOfIdentifiers(Collections.emptySet(), true));
        }
        for(Identifier id : result.getKeys())
            if(result.getState(id).elements.contains(identifier)) {
                Set<Identifier> s = new HashSet<>(result.getState(id).elements);
                s.remove(identifier);
                result = result.putState(id, new SetOfIdentifiers(s, s.isEmpty()));
            }
        return result;
    }

    @Override
    public NotEqualsDomain forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        return this;
    }

    @Override
    public Satisfiability satisfies(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        return Satisfiability.UNKNOWN;
    }

    @Override
    public NotEqualsDomain pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    @Override
    public NotEqualsDomain popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    public static class SetOfIdentifiers extends InverseSetLattice<SetOfIdentifiers, Identifier> {
        public SetOfIdentifiers(Set<Identifier> elements, boolean isTop) {
            super(elements, isTop);
        }

        @Override
        public SetOfIdentifiers mk(Set<Identifier> set) {
            return new SetOfIdentifiers(set, set.isEmpty());
        }

        @Override
        public SetOfIdentifiers top() {
            return this.mk(Collections.emptySet());
        }

        @Override
        public SetOfIdentifiers bottom() {
            return new SetOfIdentifiers(Collections.emptySet(), false);
        }
    }
}