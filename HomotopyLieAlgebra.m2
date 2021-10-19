newPackage("HomotopyLieAlgebra",                                                 
                Headline => "compute parts of the adjoint action of the homotopy Lie algebra",
                Version => "0.1",                                                
                Date => "September 21, 2021",                                        
                Authors => {                                                     
                    {Name => "David Eisenbud", Email => "email1", HomePage => "url1"},  
                    {Name => "Mike Stillman", Email => "email2", HomePage => "url2"}}, 
                DebuggingMode => true,                                          
		PackageExports => {"DGAlgebras"}
                )                                                                


export {"bracket",
	"bracketMatrix",
	"allgens"}

-* Code section *-
homdeg = f -> first degree f 
intdeg = f -> last degree f
absdeg = m -> sum(listForm m)_0_0 -- number of factors of a monomial
isSquare = m -> max (listForm m)_0_0 >=2

allgens = method()
allgens DGAlgebra := List => A -> (
    g := apply(gens((flattenRing A.natural)_0), 
               t -> sub(t, A.natural));
    sort(g, T -> homdeg T))
allgens(DGAlgebra, ZZ) := List => (A,d) -> select(allgens A, T -> homdeg T == d)		
--if V is a variable with a coefficient, we want to extract the index of the variable!

ind = V -> (keys ((keys standardForm V)_0))_0

pairing1 = method()
pairing1(List, RingElement) := RingElement => (L,M) -> (
    --L = {U,V}, where U,V are (dual) variables of A1
    --M is a monomial of absdeg 2 (possibly with nontrivial coef) in A1
    --return 0 unless M == r*U*V, where r is in CoefficientRing A1
    --Note that the monomials xy in diff(A, T_) are always written with increasing index.
    --Thus if index V > index U then <V,x> = 0, so the result is (-1)^(deg*deg)<u,x><v,y>
    (U,V) := (L_0,L_1);
    A1 := ring U;
    M2 := contract(V,M);
    if M2 == 0  then return 0_A1;
    Mcoef := contract(U,M2);
    if Mcoef == 0 then return 0_A1;
    --at this point M = cxy, with index y >= index x
    if isSquare M then if  homdeg U%2==0 then return 2*Mcoef else return 0_A1;
--    if index V < index U then Mcoef else
    if ind V < ind U then Mcoef else
    sgn := (-1)^((homdeg U)*(homdeg V)) * Mcoef
    )

pairing = method()
pairing(List, RingElement) := RingElement => (L,M) -> (
    --L = {U,V}, where U,V are scalar linear combinations of generators u, v of A1,
    --all of the same homdeg
    --M is an element of A1
    --returns the sum of the values of pairing1({u,v},m)
    (U,V) := (L_0,L_1);
    MM := select(terms M, m -> absdeg m == 2);
    UU := terms U;
    VV := terms V;
    sum apply(UU, 
	u-> sum apply(VV, 
	    v -> sum apply(MM, 
		M'-> pairing1({u,v},M'))))
     )

bracket = method()
bracket (DGAlgebra, List) := Matrix => (A,L) ->(
    --L = {U,V}, where U,V are scalar linear combinations of (dual) generators of A.natural
    --of homological degrees d-1,e-1, regarded as elements of Pi_d,Pi_e.
    --returns [U,V] 
    --as an element of Pi_(d+e), represented as a sum of the dual generators
    --of A.natural of degree i+j-1 
    if L_0 == 0 or L_1 ==0 then return 0_(A.natural);
    
    (A',toA') := flattenRing A.natural;
    fromA' := toA'^(-1);
    g' := sort(gens A', t->homdeg t); -- put the vars in order of homological degree
    A1 := coefficientRing A'[g', Degrees => g'/degree];
    ud := toList(0..max(g'/homdeg));
    toA1 := (map(A1,A')*toA');
    fromA1 := fromA'*(map(A',A1));
    (U1,V1) := (toA1 L_0,toA1 L_1); 
    g1 := select(gens A1, T->homdeg T == homdeg U1 + homdeg V1 + 1);
    sum apply(g1, T ->(
	dT := toA1 diff(A, fromA1 T);
	fromA1 ((-1)^(homdeg V1)*T*pairing({U1,V1}, dT))
	))
    )

bracketMatrix = method()
bracketMatrix (DGAlgebra, ZZ,ZZ) := Matrix => (A,d,e) -> (
    Pd := allgens(A,d-1); --dual basis of d-th homotopy group
    Pe := allgens(A,e-1); --dual basis of e-th homotopy group
    matrix apply(Pd, T -> apply(Pe, T' -> bracket(A,{T,T'})))
	    )

bracket (DGAlgebra, List, RingElement) := Matrix => (A,L,T) ->(
    --L = {U,V}, where U,V are (dual) linear forms of A.natural
    --regarded as generators of Pi and , and T is a an element of A.natural
    --returns the action of [U,V] on T
    (-1)^(homdeg L_1)*pairing(L, diff(A,T))
	)

bracket(DGAlgebra, ZZ, ZZ) := HashTable => (A,d1,d2) -> (
--    g := allgens A;
--    g1 := select(g, t -> homdeg t == d1-1); -- dual gens of Pi_d1
--    g2 := select(g, t -> homdeg t == d2-1);  -- dual gens of Pi_d2
--    g3 := select(g, t -> homdeg t == d1+d2-1); -- gens on which [Pi_d1, Pi_d2] acts
    g1 := allgens(A, d1-1);
    g2 := allgens(A, d2-1);
    g3 := allgens(A, d1+d2-1);        
    hashTable flatten flatten apply(g1, 
	u -> apply(g2, 
	    v -> apply(g3, 
		T ->( ({u,v},T) => bracket(A,{u,v},T))
		)))
    )

ad = method()
ad(DGAlgebra, RingElement, RingElement) := Matrix => (A,T,T') ->(
    --T is a sum of generators of A.natural all of the same homdeg, d-1 := homdeg T,
    --regarded as an element of Pi_(d)
    --T' is a sum of generators of A.natural all of the same homdeg, e-1 := homdeg T',
    --regarded as an element of Pi_(e)
    --ad(T)(T') is then a functional on A_(d+e-1), returned as the dual generator
     b := bracket(A,{T,T'});
     c := allgens(A, homdeg T + homdeg T' + 1)
)    


-* Documentation section *-
beginDocumentation()


doc ///
Key
 HomotopyLieAlgebra
Headline 
 Homotopy Lie Algebra of a surjective ring homomorphism
Description
  Text
   If R = S/I, K is the Koszul complex on the generators of I, and A is the DGAlgebra
   that is the acyclic closure of K, then the homotopy Lie algebra Pi of the map S -->> R
   is defined as in Briggs ****.
  Example
   S = ZZ/101[x,y]
   R = S/ideal(x^2,y^2,x*y)
   KR = koszulComplexDGA(ideal R)
  Text
   Since the acyclic closure is infinitely generated, we must specify 
   the maximum homological degree
   in which cycles will be killed
  Example
   lastCyclesDegree = 4
   A = acyclicClosure(KR, EndDegree => lastCyclesDegree)
  Text
   The evaluation of bracketMatrix(A,d,e) gives the matrix of values of [Pi^d,Pi^e]
  Example
   bracketMatrix(A,1,1)
   bracketMatrix(A,2,1)
   bracketMatrix(A,2,2)
  Text
   Note that bracketMatrix(A,d,e) is antisymmetric in d,e if one of them is even,
   and symmetric in d,e if both are odd
  Example
   bracketMatrix(A,1,1) - transpose bracketMatrix(A,1,1)
   bracketMatrix(A,2,1) + transpose bracketMatrix(A,1,2)
References 
 Briggs, Avramov
SeeAlso
///
-*
doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
  Item
Description
  Text
  Example
  CannedExample
  Code
  Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///
*-
-* Test section *-
TEST/// --graded skew symmetry:
kk = ZZ/101
S = kk[x,y]
R = S/ideal(x^2,y^2,x*y)
lastCyclesDegree = 4
KR = koszulComplexDGA(ideal R)
A = acyclicClosure(KR, EndDegree => lastCyclesDegree)
--
assert(bracketMatrix(A,1,1) - transpose bracketMatrix(A,1,1) == 0)
assert(bracketMatrix(A,2,1) + transpose bracketMatrix(A,1,2) == 0)
assert(bracketMatrix(A,2,2) + transpose bracketMatrix(A,2,2) == 0) 
assert(bracketMatrix(A,2,3) + transpose bracketMatrix(A,3,2) == 0) 
assert(bracketMatrix(A,3,3) - transpose bracketMatrix(A,3,3) == 0) 

///

///
restart
needsPackage "DGAlgebras"
loadPackage "HomotopyLieAlgebra"
///

TEST/// 
--gradedJacobi identity: 
--[U,[V,W]] = [[U,V],W] + (-1)^(1+homdeg U)*(1+homdeg V))* [V,[U,W]]

kk = ZZ/101
S = kk[x,y]
R = S/ideal(x^2,y^2,x*y)
lastCyclesDegree = 4
KR = koszulComplexDGA(ideal R)
A = acyclicClosure(KR, EndDegree => lastCyclesDegree)

n = 2
elapsedTime LL = flatten flatten flatten apply(n, d->apply(n, e-> apply(n, f->(
Pid = allgens(A,d-1);
Pie = allgens(A,e-1);
Pif = allgens(A,f-1);
L = flatten flatten flatten apply(Pid, U -> apply(Pie, V-> apply(Pif, W -> (		
bracket(A, {U,bracket(A,{V,W})}) == 
bracket(A, {bracket(A, {U,V}),W}) + (-1)^(d*e) * bracket(A, {V,bracket(A,{U,W})})
    ))));
all(L, ell ->ell)
))));
all(LL, ell->ell)
///

end--


uninstallPackage "HomotopyLieAlgebra"
restart
installPackage "HomotopyLieAlgebra"
check HomotopyLieAlgebra

viewHelp HomotopyLieAlgebra

netList path
