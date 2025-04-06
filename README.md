# TAS  
présenté par : 
-   Yanis Tabellout 
-   Salim Tabellout 
Ce projet est une implémentation des deux articles mentionnées sur : 
-   Extended Sign Domain (ref . Antoine Miné Abstract interpretation)
-   Two Variables inequality : (ax+by <=c)

Pour le module TAS qui a été présenté pour le master 2 STL à sorbonne université promo (2024/2025)

## REMARQUE : 
MALGRE QUE LES COMMITS ONT ETE SIGNEES MAJORITAIREMENT PAR UNE PERSONNE SAUF QUE LE TRAVAIL EST FAIT 
EN BINOME IN REAL LIFE

# Extended Sign Domain 
Ce projet implémente un **domaine abstrait des signes étendu** inspiré du cours d’Antoine Miné sur l’analyse statique (MPRI, chapitre 4.2), utilisant la librairie [LiSA (Library for Static Analysis)](https://lisa-tools.github.io/docs/). Il s'agit d'une extension du domaine classique des signes, permettant de capturer plus finement des propriétés numériques abstraites. On note que ceci n'est pas une implémentation dans tout les cas possibles mais qu'une fine implémentation possible parmi d'autres

## 🔍 Objectif

Analyser statiquement des programmes simples en inférant des propriétés numériques sur les variables entières (positif, négatif, zéro, etc.), en tenant compte de certaines distinctions supplémentaires, comme :

- **> 0** (strictement positif)
- **>= 0** (positif)
- **< 0** (strictement négatif)
- **<= 0** (négatif)
- **0**
- **≠ 0** (non nul)
- **⊤** (top, inconnu)
- **⊥** (bottom, contradiction)

## 🌐 Structure du domaine
- Le domaine implémente `BaseNonRelationalValueDomain<ExtendedSigns>` de LiSA.
- Les éléments du domaine sont représentés par un entier (`int sign`), chaque constante symbolise un état abstrait.
- Le domaine implémente un `Lattice` partiellement, avec notamment `lubAux` (union).
## 🏗️ Fonction principales
-   **top()/bottom()** : Renvoie ⊤ ou ⊥ respectivement
-   **lubAux()** : Union des informations abstraites
-   **evalNonNullConstant()** : Interprétation abstraite d'une constante numérique
-   **evalUnaryExpression()** : Interprétation d'une opération unaire ```(-x)```
-   **evalBinaryExpression()** : Interprétation abstraite des opérations binaires  ```(+, -, *, /)```
-   **assumeBinaryExpression()** : Raffinement d'un environnement suite à une hypothèse   ```if (x <= y)```

## Exemples 
``` basic : contient tout les cas possibles pour les opérateurs (addition, ...)```

```branch/branches: permet de mieux visualiser le lub```
```loop: visualiser le comportement dans les sortis de boucles```


# Two Variables Per Linear Inequality Domain

## 📘 Description

Cette implémentation repose sur le domaine abstrait introduit dans l'article ([Two Variables per Linear Inequality as an Abstract Domain](https://link.springer.com/chapter/10.1007/3-540-45013-0_7)).  
Le domaine abstrait ici capture des relations **linéaires** entre deux variables au plus, de la forme :
```a·x + b·y ≤ c ```
où `a`, `b`, `c` sont des constantes entières. L’objectif est d’analyser de façon plus précise les programmes contenant des contraintes linéaires binaires, souvent présentes dans les tests conditionnels, etc.

## 🧠 Structure du domaine abstrait

Le domaine est représenté comme un ensemble de contraintes linéaires à deux variables maximum. Chaque instance contient un ensemble de contrainte qui y est propre

### 🔷 Éléments du domaine
Chaque élément est un ensemble fini d'inégalités linéaires à deux variables maximum.  
Ces éléments peuvent être vus comme des **zones convexes** dans ℝ² ou ℤ².
### 🔷 Répresentation des équation 

Chaque équation est représenté 

## 🏗️ Fonctions implémentées

### `lub()` – *Least Upper Bound*
- Calcule la **plus petite sur-approximation** commune à deux ensembles d’inégalités. Cette fonction fait appelle à la fonction closure pour gérer les états transitive et éliminer les redunduncy
- Interprétation : union abstraite, dans ce cadre, nous permettant à deux égalités identiue dans les coefficients 
mais différencié par leurs constantes à prendre l'équation la plus grande (moins restrictif) qui est la plus petite valeur des deux e.g : soit les deux équations : 
```ax+by <=c``` et ```ax+by <=d```  alors :

    ```ax+by <=c``` ``U`` ```ax+by <=d``` =  ```ax+by <= max(c,d) ``` 

- pourquoi choisir le maximum dans un lub ? c'est simple, prenons l'exemple ou  vous avez un nested if par exemple 
```
if(x+y<=c){ //eq1
    if(x+y<=d){ //eq2
        st1;
    }
    st2;
}
```
Si on prenait plutôt `min(c, d)` comme résultat du LUB, alors dans le bloc st2, on retiendrait à tort la contrainte la plus restrictive `(eq2)`, alors qu'elle n’est valable que dans le bloc interne st1. Cela conduirait à une approximation trop précise, donc incorrecte pour représenter l’union abstraite des chemins. certe, nous perdons la précision, mais nous voulons toujours gardé une information qui soit plus sûr. Dans l'exemple suivant par exemple
```
    if(x+y<=c){ //eq 
        st1;
    }
    st2;
```
l'équation sera ajouté par exemple pour indiquer qu'il se peut qu'elle soit juste, on fait une analyse abstraite approché et pas précise donc vaut mieux sauvegarder cette information

### `glb()` – *Greatest Lower Bound*
- Calcule la **plus grande sous-approximation**.Cette fonction fait appelle à la fonction closureGlb pour gérer les états transitive et éliminer les redunduncy
- Interprétation : intersection abstraite, dans ce cadre, nous permettant à deux égalités identiue dans les coefficients mais différencié par leurs constantes à prendre l'équation la plus petite (plus restrictif) qui est la plus petite valeur des deux e.g : soit les deux équations : 
```ax+by <=c``` et ```ax+by <=d```  alors :

    ```ax+by <=c``` ``∩ `` ```ax+by <=d``` =  ```ax+by <= min(c,d) ``` 

### `assume()` 
Permet d'assumer les conditionnels et de générer les équations lors des entrées des conditions notamment pour la comparison (less or equal) sous la forme : 
-  **x <=y**
-  **a*x+b*y <=c**
### `assign()` 
Permet de génrer les équations lors de l'assignation notamment : 
-   **x=c** : génrera une équation sous la forme de : `x<=c`
-   **x=y** : génrera une équation sous la forme de : `x-y<=0`
-   **x=y+c** : génrera une équation sous la forme de : `x-y<=c`
-   **x=b*y+c** : génrera une équation sous la forme de : `x - b*y<=c`

# Produit Cartésien 
Pour celà, nous avons utilisé le produit cartesian qu'on a étendu directement de la classe prédéfini 

