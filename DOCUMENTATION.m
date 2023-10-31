(* ::Package:: *)

AppendTo[$Path, NotebookDirectory[]];
Needs["MINIBAR`"]


(* ::Chapter:: *)
(*Partial documentation*)


(* ::Text:: *)
(*Version 0 : A manual and basic tutorial is underway, but in this early version at least the most relevant functions are documented in standard Mathematica format. Also, the full examples contain a few comments in the workflow of the calculation.*)
(**)
(*Execute these sections to see the documentation and a few examples for some of the most relevant functions. *)


(* ::Section::Closed:: *)
(*[Doc] Helpers to debug*)


?seeChangedElements
?seeEqualElements

list1=Range[10,20];
list2=list1/._?EvenQ->0;

seeChangedElements[list1,list2]
seeEqualElements[list1,list2]


?positionDuplicates

example={a,a,b,a,b,c,d,k,k,k,k,g,g};
positionDuplicates[example]
positionDuplicates[example,2]


?compareDuplicates

list1={a1,a2,b,c,d,r,t};
list2={a,a,e,e,e,f,f};
compareDuplicates[list1,list2]
compareDuplicates[list1,list2,1]


(* ::Text:: *)
(*Find terms easily within the basis*)
(**)
(*lag//find[chim, fm]//see  (*At least one chim and one fm*)*)
(*lag//findExact[chim, fm, fm]//see (*Exactly one chim and two fm, and maybe other fields*)*)
(*lag //findWithNDer[chim,4]//see (*At least one chim with 4 der*)*)
(*lag//findWithMinNDer[chim,1]//see (*At least one chim with at least 1 der*)


?find
?findExact
?findWithNDer
?findWithMinNDer


(* ::Text:: *)
(*General helpers*)


?plusToList
a+b-c//plusToList


?inactivePower
a^3 b^4
%//inactivePower
%//Activate


(* ::Section::Closed:: *)
(*[Doc] Compose terms*)


?getCombinations
getCombinations[{a,b,c},2]


?applyDerivativesAndPermutations
applyDerivativesAndPermutations[der^2 a b]//TableForm


?sortTracesSimple
TR[11,3,99,7]TR[b,a,c]//sortTracesSimple


?applyDistributed
applyDistributed[F,Dot[a,b,c]]

?introduceTraces
introduceTraces[{{a . b . c},{X . Y},{Z}}] //TableForm


?insertIndexPlaceHolders
nIndices[chip]=0;
nIndices[fm]=2;
nIndices[fp]=2;
TR[DD[chip,1],DD[fm,2],DD[fp,0]]//insertIndexPlaceHolders


?insertIndices


?insertOneIndexCombination
term=F[a][index[1]]*G[b][index[3]]^2
insertOneIndexCombination[term,{j1,j1,m1,m2,m3,m4,m5}]


?generateIndexOrderings
generateIndexOrderings[{a,b},{A}]
generateIndexOrderings[{a},{A,B}]
generateIndexOrderings[{},{A,B}]
generateIndexOrderings[{a,b},{}]


(* ::Section::Closed:: *)
(*[Doc] Trivial relations*)


?getDictionaryOfShapes
{{a1,a2},{b1,b2},{X,Y,Z}}
%//Map[getDictionaryOfShapes]


?orderFields
?getTraceScore
?termScore


?makeIdentifyTerms


(* ::Section::Closed:: *)
(*[Doc] Operator relations*)


?getRelationsFromRule
?checkRule


(* ::Text:: *)
(*Cayley-Hamilton: automatic*)


?getCayleyHamilton


(* ::Text:: *)
(*Internally it uses*)


?getRuleCayleyHamilton


(* ::Text:: *)
(*Beyond Cayley-Hamilton: useful functions to apply rules to any product of matrices inside the traces. Also useful for Cayley-Hamilton with non-trivial transformations of the matrices (see example Anomalous ChPT LR basis)*)


?rotateTraces
?separateArgsTR
?sortGroupsCH


(* ::Text:: *)
(*Schouten*)


?getSchouten4m


(* ::Text:: *)
(*Other (mostly internal) functions*)


?removeOverallFactor
?removeOverallFactorReal
?cleanTraces


?removePatterns
?firstHead


(* ::Section::Closed:: *)
(*[Doc] Transform and reorder terms*)


?symmetrize
?signsUnder


?getTransformationRules
?getInverseTransformation


?reverseTR


?reorderOperators
?scorePreferredOperators
?getTransformationRulesFromListOrder
?moveUp
?remove


(* ::Section::Closed:: *)
(*[Doc] Gaussian Elimination*)


?getRelationMatrix


?getMinimalBasis
?getMinimalBasisAndRelations


?getRank
?getRankMathematica
?getRankMathematicaQuick


(* ::Text:: *)
(*Example SparseArray (relation matrix) to show the different getRank methods*)


n=3000; (*Increase n of elements to induce fail*)
d2=1000;
d1=600;
i=RandomInteger[{1,d1},n];
j=RandomInteger[{1,d2},n];
v=RandomInteger[{-10,10},n];
sa=SparseArray[Transpose[{i,j}]->v,{d1,d2}];
sa//MatrixPlot

getRank[sa]//showTiming
getRankMathematicaQuick[sa]//showTiming
getRankMathematica[sa]//showTiming


(* ::Section::Closed:: *)
(*[Doc] Inspect and check final basis*)


?summary


(* ::Text:: *)
(*Test completeness of single bases *)


?isCompleteAndMinimalWrt
?getRedundantOperatorsUsing


(* ::Text:: *)
(*Compare bases*)


?basesDiff
?testEquivalenceBases


(* ::Text:: *)
(*Other*)


?toOpeTagsIn


?removeTermsWith
?removeTermsWithout



