package it.unive.lisa.tutorial;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.UnaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.util.datastructures.regex.TopAtom;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class TwoVariablesInequality 	
		
		implements ValueDomain<TwoVariablesInequality> {
    public static final TwoVariablesInequality TOP = new TwoVariablesInequality(true);
    public static final TwoVariablesInequality BOTTOM = new TwoVariablesInequality(false);
    public boolean top=false,bottom=false;
    private TwoVariablesInequality(boolean top) {
        if(top)
            this.top = true;
        else 
            this.bottom = true;
        this.inequalities = new HashSet<>();
	}
    public TwoVariablesInequality(Set<LinearInequality>inequalities) {
        if(inequalities.isEmpty())
            this.top = true;
        this.inequalities = removeDuplicates(inequalities);
	}


    public TwoVariablesInequality top() {
        return TOP;
    }
    public boolean isTop(){
        return this.top;
    }
    public boolean isBottom(){
        return this.bottom;
    }

    public TwoVariablesInequality bottom() {
        return BOTTOM;
    }

    public boolean knowsIdentifier(Identifier identifier) {
        return false; 
    }
    public TwoVariablesInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    public StructuredRepresentation representation() {
        if(isTop())
            return new StringRepresentation("TOP");
        if(isBottom())
            return new StringRepresentation("BOTTOM");
        return new StringRepresentation(toString());
    }
    @Override
    public TwoVariablesInequality assume(
        ValueExpression expression,
        ProgramPoint src,
        ProgramPoint dest,
        SemanticOracle oracle) throws SemanticException {
        if (!(expression instanceof BinaryExpression))
            return this;

        // todo handle ! (<=)
        BinaryExpression binaryExpression = (BinaryExpression) expression;
        if(!(binaryExpression.getOperator() instanceof ComparisonLe))
            return this;
        SymbolicExpression left = binaryExpression.getLeft();
        SymbolicExpression right = binaryExpression.getRight();
        
        // Extraire les coefficients et constantes
        Map<Identifier, Double> coefficients = new HashMap<>();
        double constant = 0.0;
        if(left instanceof Identifier  && right instanceof Identifier){
            // On veut que la forme soit x <= y => soit transformé vers 
            // create the form for  x - y <= 0
            Identifier x = (Identifier) left;
            Identifier y = (Identifier) right;
            coefficients.put(x, 1.0);
            coefficients.put(y, -1.0);
            LinearInequality inequality = new LinearInequality(coefficients, constant);
            Set<LinearInequality> res = new HashSet<>(this.inequalities);
            if(inequality!=null){
                res.add(inequality);
            }
            System.out.println("Assuming: " + inequality.toString());
            System.out.println("Having: " + toString());
            return new TwoVariablesInequality(closureGlb(res));
        }
        // extract a, x and b from left and c from left 
        if (left instanceof BinaryExpression && right instanceof Constant) {
            constant = ((Integer)((Constant) right).getValue());
            BinaryExpression leftExpr = (BinaryExpression) left;
            if (leftExpr.getOperator() instanceof AdditionOperator && leftExpr.getLeft() instanceof BinaryExpression && leftExpr.getRight() instanceof BinaryExpression) {
                // try extract a and b, x and y
                SymbolicExpression ax = leftExpr.getLeft();
                SymbolicExpression by = leftExpr.getRight();
                BinaryExpression axExpr = (BinaryExpression) ax;
                BinaryExpression byExpr = (BinaryExpression) by;
                if(axExpr.getOperator() instanceof MultiplicationOperator && byExpr.getOperator() instanceof MultiplicationOperator && axExpr.getLeft() instanceof Constant && axExpr.getRight() instanceof Identifier) {
                    SymbolicExpression a = axExpr.getLeft();
                    SymbolicExpression x = axExpr.getRight();
                    SymbolicExpression b = byExpr.getLeft();
                    SymbolicExpression y = byExpr.getRight();
                    coefficients.put((Identifier) y, ((Integer)((Constant) b).getValue()).doubleValue());
                    coefficients.put((Identifier) x, ((Integer)((Constant) a).getValue()).doubleValue());
                    LinearInequality inequality = new LinearInequality(coefficients, constant);
                    Set<LinearInequality> res = new HashSet<>(this.inequalities);
                    if(inequality!=null){
                        res.add(inequality);
                    }
                    System.out.println("Assuming: " + inequality.toString());
                    System.out.println("Having: " + toString());
                    // return bottom();
                    return new TwoVariablesInequality(closureGlb(res));
                } 
                
                
            }
        }
        return this; 
    }
    public static boolean isSpecialIdentifier(Identifier id) {
        return id.toString().contains("heap") || id.toString().contains("this") || id.toString().contains("&pp@");
    }
    public TwoVariablesInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint pp,
        SemanticOracle oracle) throws SemanticException {
        if(isSpecialIdentifier(identifier))
            return this;
        if(valueExpression instanceof Identifier){
            Identifier id = (Identifier) valueExpression;
            Map<Identifier, Double> coefficients = new HashMap<>();
            coefficients.put(identifier, 1.0);
            coefficients.put(id, -1.0);
            LinearInequality inequality = new LinearInequality(coefficients, 0.0);
            Set<LinearInequality> res = new HashSet<>(this.inequalities);
            res.add(inequality);
            System.out.println("Assigning: " + inequality.toString());
            System.out.println("Having: " + toString());
            return new TwoVariablesInequality(closureGlb(res));
        }
        if(valueExpression instanceof Constant){
            Constant c = (Constant) valueExpression;
            Map<Identifier, Double> coefficients = new HashMap<>();
            coefficients.put(identifier, 1.0);
            LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
            Set<LinearInequality> res = new HashSet<>(this.inequalities);
            res.add(inequality);
            System.out.println("Assigning: " + inequality.toString());
            System.out.println("Having: " + toString());
            return new TwoVariablesInequality(closureGlb(res));
        }
        if(valueExpression instanceof BinaryExpression){
            BinaryExpression binaryExpression = (BinaryExpression) valueExpression;
            // On veut que la forme soit x = y + c 
            if(binaryExpression.getOperator() instanceof AdditionOperator && binaryExpression.getLeft() instanceof Identifier && binaryExpression.getRight() instanceof Constant){
                // On veut que la forme soit x = y + c => soit transformé vers 
                // create the form for  x - y <= c
                Identifier y = (Identifier) binaryExpression.getLeft();
                Constant c = (Constant) binaryExpression.getRight();
                Map<Identifier, Double> coefficients = new HashMap<>();
                coefficients.put(identifier, 1.0);
                coefficients.put(y, -1.0);
                LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
                Set<LinearInequality> res = new HashSet<>(this.inequalities);
                res.add(inequality);
                System.out.println("Assigning: " + inequality.toString());
                System.out.println("Having: " + toString());
                return new TwoVariablesInequality(closureGlb(res));
            }
            // handle the case of x = b*y + c
            if(binaryExpression.getOperator() instanceof AdditionOperator &&  binaryExpression.getRight() instanceof Constant){
                if((binaryExpression.getLeft() instanceof BinaryExpression)){
                    BinaryExpression leftExpr = (BinaryExpression) binaryExpression.getLeft();
                    if((leftExpr.getOperator() instanceof MultiplicationOperator) && leftExpr.getLeft() instanceof Constant && leftExpr.getRight() instanceof Identifier){
                        // On veut que la forme soit x = b*y + c => soit transformé vers 
                        // create the form for  x - b*y <= c
                        Constant b = (Constant) leftExpr.getLeft();
                        Identifier y = (Identifier) leftExpr.getRight();
                        Constant c = (Constant) binaryExpression.getRight();
                        Map<Identifier, Double> coefficients = new HashMap<>();
                        coefficients.put(identifier, 1.0);
                        coefficients.put(y, -((Integer)b.getValue()).doubleValue());
                        LinearInequality inequality = new LinearInequality(coefficients, (Integer)(c.getValue()));
                        Set<LinearInequality> res = new HashSet<>(this.inequalities);
                        res.add(inequality);
                        System.out.println("Assigning: " + inequality.toString());
                        System.out.println("Having: " + toString());
                        return new TwoVariablesInequality(closureGlb(res));
                    }
                }
                
                
            
            }
        }
        return this;
    }

    public Set<LinearInequality> removeDuplicates(Set<LinearInequality> inequalities) {
        // GO TRHOW the inequalities and remove the equivalent ones 
        Set<LinearInequality> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            boolean isEquivalent = false;
            for (LinearInequality existingInequality : result) {
                if (inequality.equals(existingInequality)) {
                    isEquivalent = true;
                    break;
                }
            }
            if (!isEquivalent) {
                if(inequality.coefficients.size() == 0 
                || (inequality.coefficients.size() == 1 && inequality.coefficients.values().
                        stream().anyMatch(v -> v == 0.0))) {
                    // Skip the inequality if it has a coefficient of  in format 0x <= c
                    continue;
                }
                result.add(inequality);
            }
        }
        return result;
    }
    public Set<LinearInequality> closureLub(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> result = new HashSet<>(inequalities);
        // Étape 1: Supprimer les inégalités redondantes (même coefficient, constante différente)
        result = lubLinearInequality(inequalities); 
        // Étape 2: Appliquer la transitivité pour générer de nouvelles inégalités
        Set<LinearInequality> newInequalities = transitivity(result);
        // Ajouter les nouvelles inégalités au résultat
        result.addAll(newInequalities);
        // Étape 3: Nettoyer à nouveau les redondances après l'ajout des nouvelles inégalités
        result = lubLinearInequality(result);
        return result;
    }
    public Set<LinearInequality> closureGlb(Set<LinearInequality> inequalities) {
        Set<LinearInequality> result = new HashSet<>(inequalities);
        result = glbLinearInequality(inequalities); 
        Set<LinearInequality> newInequalities = transitivity(result);
        result.addAll(newInequalities);
        result = glbLinearInequality(result);
        return result;
    }
    public Set<LinearInequality> transitivity(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> newInequalities = new HashSet<>();
        for (LinearInequality ineq1 : inequalities) {
            for (LinearInequality ineq2 : inequalities) {
                if (ineq1.equals(ineq2)) continue;
                // Trouver des variables communes entre les deux inégalités
                Set<Identifier> commonVars = new HashSet<>(ineq1.var());
                commonVars.retainAll(ineq2.var());
                if (!commonVars.isEmpty()) {
                    // Pour chaque variable commune, essayer de dériver une nouvelle inégalité
                    for (Identifier commonVar : commonVars) {
                        Double coef1 = ineq1.coefficients.get(commonVar);
                        Double coef2 = ineq2.coefficients.get(commonVar);
                        boolean hasDifferentSign = coef1 * coef2 < 0;
                        // Vérifier si les coefficients ont le même signe
                        if (hasDifferentSign ) {
                            // Créer une nouvelle inégalité combinée
                            Map<Identifier, Double> newCoeffs = new HashMap<>();
                            double scale1 = Math.abs(coef2);
                            double scale2 = Math.abs(coef1);
                            // Ajouter les coefficients mis à l'échelle de la première inégalité
                            for (Map.Entry<Identifier, Double> entry : ineq1.coefficients.entrySet()) {
                                Identifier var = entry.getKey();
                                if (!var.equals(commonVar)) {
                                    newCoeffs.put(var, entry.getValue() * scale1);
                                }
                            }
                            // Ajouter les coefficients mis à l'échelle de la seconde inégalité
                            for (Map.Entry<Identifier, Double> entry : ineq2.coefficients.entrySet()) {
                                Identifier var = entry.getKey();
                                if (!var.equals(commonVar)) {
                                    double existingCoef = newCoeffs.getOrDefault(var, 0.0);
                                    newCoeffs.put(var, existingCoef + entry.getValue() * scale2);
                                }
                            }
                            
                            // Calculer la nouvelle constante
                            double newConstant = ineq1.constant * scale1 + ineq2.constant * scale2;
                            
                            // Créer la nouvelle inégalité et l'ajouter aux résultats
                            LinearInequality newIneq = new LinearInequality(newCoeffs, newConstant);
                            newInequalities.add(newIneq);
                        }
                    }
                }
            }
        }
        return newInequalities;
       
    }
    /*
     * 
     * * Implémente l'opérateur de jointure lub pour les inégalités linaires 
     * e.g: ax + by <= c et ax + by <= d => ax + by <= min(c,d) e.g : 
     */
    public Set<LinearInequality> lubLinearInequality(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> result = new HashSet<>(inequalities);
        // Étape 1: Supprimer les inégalités redondantes (même coefficient, constante différente)
        Map<String, LinearInequality> coeffToIneq = new HashMap<>();
        // Regrouper par coefficients et garder seulement l'inégalité la plus restrictive
        // exemple si tu sais que x <= 5 et x <= 10, tu gardes x <= 5 
        for (LinearInequality ineq : result) {
            // Créer une clé représentant la structure des coefficients
            StringBuilder keyBuilder = new StringBuilder();
            for (Map.Entry<Identifier, Double> entry : ineq.coefficients.entrySet()) {
                keyBuilder.append(entry.getKey().getName())
                        .append(":")
                        .append(entry.getValue())
                        .append(";");
            }
            String key = keyBuilder.toString();
            // Conserver seulement l'inégalité avec la plus grande constante
            if (!coeffToIneq.containsKey(key) || coeffToIneq.get(key).constant <= ineq.constant) {
                coeffToIneq.put(key, ineq);
            }
        }
        return new HashSet<>(coeffToIneq.values());
    }
    public Set<LinearInequality> glbLinearInequality(Set<LinearInequality> inequalities) {
        // Copier les inégalités initiales dans le résultat
        Set<LinearInequality> result = new HashSet<>(inequalities);
        // Étape 1: Supprimer les inégalités redondantes (même coefficient, constante différente)
        Map<String, LinearInequality> coeffToIneq = new HashMap<>();
        // Regrouper par coefficients et garder seulement l'inégalité la plus restrictive
        // exemple si tu sais que x <= 5 et x <= 10, tu gardes x <= 5 
        for (LinearInequality ineq : result) {
            // Créer une clé représentant la structure des coefficients
            StringBuilder keyBuilder = new StringBuilder();
            for (Map.Entry<Identifier, Double> entry : ineq.coefficients.entrySet()) {
                keyBuilder.append(entry.getKey().getName())
                        .append(":")
                        .append(entry.getValue())
                        .append(";");
            }
            String key = keyBuilder.toString();
            // Conserver seulement l'inégalité avec la plus grande constante
            if (!coeffToIneq.containsKey(key) || coeffToIneq.get(key).constant > ineq.constant) {
                coeffToIneq.put(key, ineq);
            }
        }
        return new HashSet<>(coeffToIneq.values());
    }
    public TwoVariablesInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        // Handle different types of expressions
        return this;
    }
    @Override
    public boolean lessOrEqual(TwoVariablesInequality other) throws SemanticException {
        return false;
    }
    @Override
    public TwoVariablesInequality lub(TwoVariablesInequality other) throws SemanticException {
        // union est l'intersection des deux ensembles 
        if(isTop())
            return other;
        if(other.isTop())
            return this;
        if(isBottom())
            return other;
        if(other.isBottom())
            return this;
         // Créer un nouvel ensemble qui est l'union des deux ensembles d'inégalités
        Set<LinearInequality> unionInequalities = new HashSet<>(this.inequalities);
        unionInequalities.addAll(other.inequalities);
        var l = new TwoVariablesInequality(closureLub(removeDuplicates(unionInequalities)));
        return l;
    }
    @Override
    public TwoVariablesInequality glb(TwoVariablesInequality other) throws SemanticException {
        if (isTop()) return other;
        if (other.isTop()) return this;
        if (isBottom() || other.isBottom()) return BOTTOM;
        Set<LinearInequality> result = new HashSet<>(this.inequalities);
        result.addAll(other.inequalities);
        return new TwoVariablesInequality(closureGlb(removeDuplicates(result)));
    }

    
    public Set<Identifier> vars() {
        Set<Identifier> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            result.addAll(inequality.var());
        }
        return result;
    }
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        boolean first = true;
        
        for(LinearInequality inequality : inequalities) {
            if(!first)
                sb.append(", ");
            sb.append(inequality.toString());
            first = false;
        }
        sb.append("}");
        return sb.toString();
    }


     /**
     * Implémente l'opérateur de restriction πY défini dans l'article
     * πY(T) = {t ∈ T | var(t) ⊆ Y}
     */
    public Set<LinearInequality> restrictTo(Set<Identifier> variables) {
        Set<LinearInequality> restricted = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            if (variables.containsAll(inequality.var())) {
                restricted.add(inequality);
            }
        }
        return restricted;
    }
    public Set<LinearInequality> inequalities=new HashSet<>();


    /**
     * Classe représentant une inégalité linéaire ax + by ≤ c
    */
    public static class LinearInequality {
        // Coefficients des variables (ax + by)
        public Map<Identifier, Double> coefficients;
        public boolean lessOrEqual = true;
        // Constante c dans ax + by ≤ c
        private double constant;

        public LinearInequality(Map<Identifier, Double> coefficients, double constant) {
            this.coefficients = new HashMap<>(coefficients);
            this.constant = constant;
        }
        public void setLessOrEqual(boolean lessOrEqual) {
            this.lessOrEqual = lessOrEqual;
        }
        public boolean isEqualCoefficients(LinearInequality other) {
            return this.coefficients.equals(other.coefficients);
        }
      
        /**
         * Implémente la fonction var(ax + by ≤ c) comme définie dans l'article
         */
        public Set<Identifier> var() {
            Set<Identifier> result = new HashSet<>();
            for (Map.Entry<Identifier, Double> entry : coefficients.entrySet()) {
                double coef = entry.getValue();
                if(coef != 0)
                    result.add(entry.getKey());
            }
            return result;
        }
        public boolean equals(LinearInequality other) {
            if (this == other) return true;
            return coefficients.equals(other.coefficients) && constant == other.constant;
        }
     

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            boolean first = true;
            
            for (Map.Entry<Identifier, Double> entry : coefficients.entrySet()) {
                double coef = entry.getValue();
                if (!first && coef > 0) sb.append(" + ");
                else if (!first) sb.append(" - ");
                else if (coef < 0) sb.append("-");
                
                if (Math.abs(Math.abs(coef) - 1.0) > 0.0001) {
                    sb.append(Math.abs(coef)).append("*");
                }
                
                sb.append(entry.getKey().getName());
                first = false;
            }
            if(lessOrEqual)
                sb.append(" <= ");
            else
                sb.append(" < ");
            sb.append(constant);
            return sb.toString();
        }
    }


    public TwoVariablesInequality close() {
        TwoVariablesInequality result = this;
       
        return result;
    }
    public TwoVariablesInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        TwoVariablesInequality result = this;
        
        return result;
    }

    public Satisfiability satisfies(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        return Satisfiability.UNKNOWN;
    }




}
