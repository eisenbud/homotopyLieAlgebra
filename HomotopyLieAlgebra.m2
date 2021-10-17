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


export {"pairing",
        "bracket"}

-* Code section *-
homdeg = f -> first degree f 
intdeg = f -> last degree f
absdeg = m -> sum(listForm m)_0_0 -- number of factors of a monomial
isSquare = m -> max (listForm m)_0_0 >=2

pairing = method()
pairing(List, RingElement) := RingElement => (L,M) -> (
    --L = {U,V}, where U,V are (dual) variables of A1
    --M is a monomial of absdeg 2 (possibly with nontrivial coef) in A1
    --return 0 unless M == r*U*V, where r is in CoefficientRing A1
    (U,V) := (L_0,L_1);
    M2 := contract(V,M);
    if M2 == 0  then return 0;
    Mcoef := contract(U,M2);
    if Mcoef == 0 then return 0;
    --at this point U and V are the variables that are factors of M
    if isSquare M then return 2*Mcoef;
    sgn := (-1)^(homdeg V % 2);
    sgn' := if index U >= index V then 1 else -1;
    (sgn,sgn',sgn*sgn'*Mcoef))

bracket = method()
bracket (DGAlgebra, List) := Function => (A,L) ->(
    --L = {U,V}, where U,V are (dual) variables of A.natural of degrees i+1 and j+1,
    --regarded as generators of Pi^i and Pi^j.
    --returns the action of [U,V] on the elements of A.natural
    --that have homological degree homdeg U + homdeg V - 1.
    (U,V) := (L_0,L_1);
    Anatural := ring U;
    (A',toA') := flattenRing Anatural;
    fromA' := toA'^(-1);
    g' := (gens A');
    ud := toList(0..max(g'/homdeg));
    gg' := apply(ud, i-> select(g', T -> homdeg T == i)); 
    --now gg'_i is the list of variables of homological degree i in A.natural, in order of homdeg
    A1 := coefficientRing A' [ flatten gg', Degrees => (flatten gg')/degree ]; -- now variables are in order by homol degree.
    toA1 := (map(A1,A')*toA');
    fromA1 := fromA'*(map(A',A1));
    gg1 := apply(ud, i-> select(gens A1, T -> homdeg T == i));

    map(Anatural^1, 
	Anatural^(-(flatten gg1)/degree), 
	apply(flatten gg1, T ->(
		dT := diff(A, T);
        	dT2 := select(terms dT, m -> absdeg m == 2);
		fromA1 (pairing({toA1 U,toA1 V}, toA1 dT2))))
	)
    )


///
restart
debug needsPackage "DGAlgebras"
loadPackage "HomotopyLieAlgebra"
kk = ZZ/101
S = kk[x,y,z]
R = S/ideal(x^2,x*y,y^2,z^2)
A = acyclicClosure (R,EndDegree => 3)
cA = toComplex(A,4)
cA.dd
A.natural
#degrees A.natural
diff_A (T_3)
B3 = getBasis(3,A)
d = cA.dd_4
vars4 = select(gens A.natural, t->first degree t == 4)
vars2 = select(gens A.natural, t->first degree t == 2)
vars1 = select(gens A.natural, t->first degree t == 1)
M = for i from 0 to 4 list matrix {select(gens A.natural, t->first degree t == i)}
dM4 = matrix {for t in vars4 list diff_A(t)}
isHomogeneous dM4
diff(transpose matrix M_1, dM4)
prod = diff (transpose gens (ideal(M#1)*ideal(M#2)), dM4)


map(R,A.natural,sub(vars A.natural - vars A.natural, R))
phi = map(R,A.natural, toList(12:0_R), DegreeMap => d -> drop(d,1))
kkk = kk[ DegreeRank => 1]
degrees source M_1
R/(ideal vars R)**source M_1
degrees oo
jmap(transpose phi prod


restart
debug needsPackage "DGAlgebras"
loadPackage "HomotopyLieAlgebra"
kk = ZZ/101
S = kk[x,y]
R = S/ideal(x^5,y^2,x*y)
lastCyclesDegree = 4


ud = toList(0..lastCyclesDegree+1) -- degrees of the potential variables
KR = koszulComplexDGA(ideal R)
A = acyclicClosure(KR, EndDegree => lastCyclesDegree)
(A',toA') = flattenRing A.natural
fromA' = toA'^(-1)
g' = (gens A')
d' = g'/degree
gg' = apply(ud, i-> select(g', T -> homdeg T == i))
--now gg1_i is the list of variables of homological degree i in A'
A1 = coefficientRing A' [ flatten gg', Degrees => (flatten gg')/degree ] -- now variables are in order by homol degree.
toA1 = (map(A1,A')*toA')
fromA1 = fromA'*(map(A',A1))
gg1 = apply(ud, i-> select(gens A1, T -> homdeg T == i))
assert(isHomogeneous fromA1 and isHomogeneous toA1)

f = toA1 diff(A, fromA1 T_7)
qf = select(terms f, m -> absdeg m == 2)

m = -3*A1_3*A1_7
n = 7* gg1_2_0^2
degree m
degree  n
isSquare m
isSquare n
(terms f)/absdeg

use A.natural    
A.natural === ring T_2
source (bracket {T_2,T_6})
(bracket {T_2,T_6}) (fromA1 m)
ring (fromA1 m) ===A.natural

use A1    
m,pairing ({T_1,T_6},m)
m,pairing ({T_2,T_6},m)
m,pairing ({T_6,T_2},m)


n,pairing ({T_5,T_4},n)
n,pairing ({T_4,T_4},n)


    
A1.dd
B = acyclicClosure (A1, EndDegree =>5)
toComplex (B,5)
B.dd
dgAlgebraMap(A1,B,matrix{{T_1,T_2,0,0,0}})
A1.natural
map((A1.natural)^1,, matrix{{A1.natural_0,A1.natural_1}|toList(25:0)})
dgAlgebraMap(A1, B, oo)
isWellDefined oo
methods (dgAlgebraMultMap, B, )
peek B.cache.diffs
HH B
B.dd
peek A1

A = freeDGAlgebra(S,{{1,2},{1,2}})
prune HH(6,B)
isGolod R


setDiff(A,flatten entries presentation R)


///

-* Documentation section *-
beginDocumentation()

-*
doc ///
Key
 HomotopyLieAlgebra
Headline
 Adjoint action of the homotopy Lie algebra of a local homomorphism
Description
  Text
  Tree
  Example
  CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

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
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

installPackage "HomotopyLieAlgebra"
