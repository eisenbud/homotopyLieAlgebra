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


export {}

-* Code section *-
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
R = S/ideal(x^2,y^2,x*y)
KR = koszulComplexDGA(ideal R)
A1 = acyclicClosure(KR, EndDegree => 4)

A1.natural
toComplex(
    
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
