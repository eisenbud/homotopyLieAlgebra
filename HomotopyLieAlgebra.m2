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
kk = ZZ/101
S = kk[x,y]
R = S/ideal(x^2,x*y,y^2)
A1 = freeDGAlgebra(R,{{1,1},{1,1}})
setDiff(A1,gens R)
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
