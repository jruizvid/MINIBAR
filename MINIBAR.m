(* ::Package:: *)

(* ::Section:: *)
(*MINIBAR*)


(* ::Text:: *)
(*Tools to calculate minimal operator bases rapidly with Mathematica*)
(*version 0: October 31st, 2023*)
(**)
(*Author: Joan Ruiz-Vidal (Lund University)*)


(* ::Section::Closed:: *)
(*Declaration*)


(* ::Text:: *)
(*This software provides a set of tools to aid the calculation of operator bases in QFT Lagrangians.*)
(*These tools have been developed for the case of Chiral Perturbation Theory (ChPT) with pseudoscalar mesons and external fields, and, in particular, to obtain the anomalous Lagrangian of ChPT at order p6/p8. The two given examples of minimal bases (in version 0) lead to the final result, written in two different parametrizations of the field content.*)
(**)
(*The underlying algorithms and structure of the calculation has been shaped in collaboration with *)
(* - Johan Bijnens (Lund University)*)
(* - Nils Hermansson-Truedsson (Lund University; Edinburgh University) *)
(**)
(*Both of them posses extensive expertise in these analyses and conducted independent calculations of this Lagrangian with a different software.*)
(**)
(*Crucial inputs for constructing and optimizing part of the code presented here were generously provided by the community of mathematica.stackexchange.com.*)


(* ::Section::Closed:: *)
(*Overview*)


(* ::Text:: *)
(*Usage:*)
(* - In your notebook, import the MINIBAR package adding its directory to $Path and calling Needs["MINIBAR`"]*)
(* - The Example calculations use the functions defined in "Core functions" (genuine MINIBAR), and in the section "Configuration" of the example file (user defined)*)
(*  *)
(* Overview:*)
(*The structure of the sections is the same in the main MINIBAR.m, with all the function definitions, in the documentation MINIBAR_DOC.m, and in the example calculations:*)
(* - "Compose terms" constructs the possibleTerms. Fields and derivatives are combined, traces applied and indices distributed in all the possible combinations.*)
(* - "Trivial relations" reduces the list of possibleTerms accounting for obvious zeroes, permutations of indices and cyclicity of traces.*)
(* - "Operator relations" builds the relations between terms, based on some identities given by the user. Helper functions to include Cayley-Hamilton trace relations, Total derivatives, and the Schouten identity are native in MINIBAR.*)
(* - "Transform and reorder terms" redefines the basis to make every operator Hermitian, and optionally also even under a set of user-defined discrete symmetries (P,C). It also determines which operators should be preferentially kept in the final basis*)
(* - "Gaussian elimination" finds the minimal basis from the set of operator relations*)
(* *)
(*Notation of the fields:*)
(*  - DD[field, n][a,b,...] for a field with n covariant derivatives The indices {a,b,...} belong to the derivatives and the field itself, in order.*)
(**)


(* ::Chapter:: *)
(*Configure paths*)


BeginPackage["MINIBAR`"]


$HistoryLength=3; (*Don't waste RAM*)


pathToSuiteSparse="/home/etlar/joan/Programs/SuiteSparse-7.0.1";


directoryOfMINIBAR = If[$InputFileName == "", NotebookDirectory[], DirectoryName@$InputFileName];


(* ::Chapter:: *)
(*Core functions*)


(* ::Section::Closed:: *)
(*[Functions] Helpers to debug*)


(* ::Subsection:: *)
(*General helpers*)


(* ::Subsubsection::Closed:: *)
(*Save / import data*)


(* ::Text:: *)
(*To save data use DumpSave*)


Clear[import]
import[file_]:=Get[NotebookDirectory[]<>"/save/"<>file<>".mx"]

import::usage=
"import[file_] imports the file file.mx from /save/ folder in the Notebook directory";


(* ::Subsubsection::Closed:: *)
(*Change headers, deactivate Power and Times*)


Clear[plusToList]
plusToList=If[Head[#]===Plus&&Head[#]=!=List,List@@#,If[Head[#]=!=List,List@#,#]] &;

plusToList::usage = 
"plusToList returns the list of summands in a expression with head Plus. 
Inverse of Total: y //plusToList //Total = y";


(* ::Text:: *)
(*Map any expression at level n*)


MakeExpression[RowBox[{f_,SubscriptBox["/@",n_],expr_}],StandardForm]:=MakeExpression@RowBox[{"Map","[",f,",",expr,",","{",n,"}","]"}]
(*list={{a,b},{d,{g,y},h,y},{q,r,w}};
\!\(F
\*SubscriptBox[\(/@\), \(2\)]list\)*)


Clear[inactivePower]
inactivePower[expr_]:=expr/.Power[a_,b_?IntegerQ]:>(Inactive[Times]@@ConstantArray[a,b])

inactivePower::usage = 
"inactivePower[expr_] turns every Power in expr into an explicit product and freezes its order";


(* ::Subsection:: *)
(*Debugging*)


(* ::Subsubsection::Closed:: *)
(*showTiming, showLength*)


Clear[showTiming]
showTiming[in_]:=Block[{res},res=AbsoluteTiming[in];Print[res[[1]]," s"];res[[2]]]
SetAttributes[showTiming,HoldAll] (* <-IMPORTANT!*)

showLength[in_]:=Block[{res},res=in;Print[Length[res]," terms"];res]
SetAttributes[showLength,HoldAll] 

showLengthNo0[in_]:=Block[{res},res=in;Print[Count[res,_?(#=!=0&)]," terms"];res]
SetAttributes[showLengthNo0,HoldAll] 

showLengthFlat[in_]:=Block[{res},res=in;Print[Length[Flatten[res]]," terms"];res]
SetAttributes[showLength,HoldAll] 

showTiming::usage=
"showTiming[in_] prints evaluation time, returns result. Similar to EchoFunction[AbsoluteTiming][in]";

showLength::usage=
"showLength[in_] prints the Length of the result, returns result. Similar to EchoFunction[Length][in]";

showLengthNo0::usage=
"showLengthNo0[in_] prints the number of nonzero elements, returns result. Similar to EchoFunction[Length][in]";

showLengthFlat::usage=
"showLengthFlat[in_] prints the number of elements when all sublists have been merged with Flatten. Similar to EchoFunction[(Length@Flatten@#)&][in]";


(* ::Subsubsection::Closed:: *)
(*see: Notation*)


(* ::Text:: *)
(*To inspect the terms we define the function "see". To use it, the user must define two functions*)
(*  - "nIndices[field]" gives the number of indices of each field -  is defined with the information inside BB (building blocks). [NOT ANYMORE]*)
(*  - "cal[field]" gives the calligraphic symbol of each field*)


Clear[readableNotation]
readableNotation[expr_]:=expr/.DD[field_,nder_][ind___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
nInd=Length[{ind}]-nder;
Which[
nInd==0 &&nder==0,cal[field] ,
nInd==0 &&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (cal[field]),
nInd!= 0&&nder==0, Subscript[cal[field], Sequence@@List[indMod]],
nInd!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}] . (Subscript[cal[field], Sequence@@List[indMod][[nder+1;;nder+nInd]]])])

Clear[readableIndex]
readableIndex[index_] := index /. {i_Symbol[n_Integer] :> ToString[i] <> ToString[n]}

readableNotation::usage=
"readableNotation[expr_] converts the inputform/fullform notation of fields DD[field, nderivatives][indices] 
into nice readable notation. 

Mostly INTERNAL function, used by 'see', but can be used to export expressions with a readable format, albeit 
quite complicated to work with.

To see with the same ordering of Times in expr: expr/.Times:>Dot//readableNotation";

readableIndex::usage = 
"readableIndex[index_] converts indices like j[1] or m[3] inside expressions into j1 and m3. Used by readableNotation";


Clear[seeReturn]
seeReturn[expr_]:=expr//readableNotation//TableForm;

Clear[see]
see[expr_]:=expr//EchoFunction[seeReturn]

seeReturn::usage = 
"seeReturn[expr_] converts expr into the format of see (readableNotation on a TableForm)";

see::usage = 
"see[expr_] prints expr in a nice readable format, returning expr. 

Needs user-defined function 'cal', which returns the calligraphic symbol of each field, e.g.

cal[expr_]:=expr/.{fm:>SuperMinus[\[ScriptF]],fp:>SuperPlus[\[ScriptF]],chim:>SuperMinus[\[Chi]],chip:>SuperPlus[\[Chi]],u:>\[ScriptU]}";


(* ::Subsubsection::Closed:: *)
(*Show changed and unchanged elements in list *)


Clear[seeChangedElements]
seeChangedElements[list1_,list2_]:=Module[{dif={},number=1},
If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];
Do[If[list1[[i]]=!=list2[[i]],AppendTo[dif,{number++,i,list1[[i]],list2[[i]]}],{}],
{i,Length[list1]}];
Print[Length[dif],"  changes"];
Print["|\[NumberSign]| Position | list1 | list2 |"];
dif//seeReturn]

seeChangedElements[list1_,list2_, a_?IntegerQ]:=seeChangedElements[list1,list2][[1]][[1;;a]]//seeReturn

Clear[seeEqualElements]
seeEqualElements[list1_,list2_]:=Module[{dif={},number=1},
If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];
Do[If[list1[[i]]===list2[[i]],AppendTo[dif,{number++,i,list1[[i]],list2[[i]]}],{}],
{i,Length[list1]}];
Print[Length[dif],"  equal elements"];
Print["|\[NumberSign]| Position | list1 | list2 |"];
dif//seeReturn]

seeEqualElements[list1_,list2_, a_?IntegerQ]:=seeEqualElements[list1,list2][[1]][[1;;a]]//seeReturn

seeChangedElements::usage = 
"seeChangedElements[list1_,list2_] returns a formated list of the elements in list1 and list2 that are different,
while occupying the same position in the lists. 
Given a third argument n_ (integer), returns only the first n different elements";

seeEqualElements::usage = 
"seeEqualElements[list1_,list2_] returns a formated list of all the elements in list1 and list2 that are identical,
while occupying the same position in the lists. 
Given a third argument n_ (integer), returns only the first n identical elements";


(* ::Subsubsection::Closed:: *)
(*Get positions of duplicates*)


Clear[positionDuplicates]
positionDuplicates[list1_]:=GatherBy[Range@Length[list1],list1[[#]]&]//Cases[#,{_,__}]&
positionDuplicates[list1_,nDup_?IntegerQ]:=positionDuplicates[list1]//Select[Length[#]==nDup&]


positionDuplicates::usage = 
"positionDuplicates[list1_] returns, in sublists, the position of all duplicates in list1.

Given a second argument, nDup_ (integer), it returns only duplicates found nDup times";


Clear[compareDuplicates]
compareDuplicates[list1_,list2_]:=Module[{posd1,posd2,posd},
If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];

posd1=positionDuplicates[list1]//Cases[{_,__}];
posd2=positionDuplicates[list2]//Cases[{_,__}];

posd=Complement[posd2,posd1];
If[Length[posd]>0,
Print[Length[posd]," categories of elements became duplicates in the 2nd list."], 
Print["0 new duplicates in the 2nd list"]];

Table[{list1[[position]],"\[Rule]" list2[[position//First]]},{position,posd}]//seeReturn
]

compareDuplicates[list1_,list2_, a_?IntegerQ]:=compareDuplicates[list1,list2][[1]][[1;;a]]//seeReturn

compareDuplicates::usage=
"compareDuplicates[list1_,list2_] prints which elements that were disctinct in list1 have become duplicates in list 2.
Given a third argument n_ (integer), prints only n examples of new duplicates.";


(* ::Subsubsection::Closed:: *)
(*Search terms by field content*)


Clear[find,findExact]
find[fields__][terms_List]:=Module[{tally=Tally[{fields}]},
Select[terms,(And@@Table[Count[#,DD[tally[[i,1]],_][___],99]>=1,{i,Length[tally]}])& ]]

findExact[fields__]:=Module[{tally=Tally[{fields}]},
Select[#,(And@@Table[Count[#,DD[tally[[i,1]],_][___],99]==tally[[i,2]],{i,Length[tally]}])& ]&]

Clear[findWithNDer]
findWithNDer[field_,nder_][terms_List]:=Module[{},
Select[terms,
((Count[#,DD[field,nder][___],99]>=1)&)
 ]
]

Clear[findWithMinNDer]
findWithMinNDer[field_,nder_][terms_List]:=Module[{},
Select[terms,
((Count[#,DD[field,_?(#>=nder&)][___],99]>=1)&)
 ]
]


find::usage=
"find[fields__][terms_List] returns the terms that contain at least one instance of each of the fields";
findExact::usage = 
"findExact[fields__][terms_List] returns the terms that contain these fields, accounting for repetitions, 
and possibly some other field different than those in the argument";
findWithNDer::usage = 
"findWithNDer[field_,nder_][terms_List] will find the terms that contain at least one instance of the 
field with *exactly* nder covariant derivatives. Alternatives may be given as field1 | field2 | field3";
findWithMinNDer::usage = 
"findWithMinNDer[field_,nder_][terms_List] will find the terms that contain at least one instance of the 
field with *at least* nder covariant derivatives attached to it. 
Alternatives may be given as field1 | field2 | field3";



(* ::Section:: *)
(*[Functions] Compose terms*)


(* ::Subsection:: *)
(*Build terms*)


(* ::Subsubsection::Closed:: *)
(*Get Combinations*)


(* ::Text:: *)
(*getCombinations of 2,...,m building blocks.*)


(*https://mathematica.stackexchange.com/questions/276141/working-with-tables-add-new-level-of-nested-tables*)

Clear[getCombinations]
getCombinations[factors_,m_Integer]:=Module[{list,  n=Length[factors]},
list=FrobeniusSolve[ConstantArray[1,n],m];
Inner[Power,factors,#,Times]&/@list//Sort]


getCombinations::usage = "getCombinations[list_,n_] generates the possible combinations of n elemens in the list";



(* ::Subsubsection::Closed:: *)
(*Apply derivatives and permutations*)


(* ::Text:: *)
(*Get list of fields. Compute all fieldPermutations. Possible combinations of nder derivatives over nfields. Introduce derivatives as DD[f,1]. Freeze ordering with Dot.*)


Clear[applyDerivativesAndPermutations]
applyDerivativesAndPermutations[term_]:=Module[{termaux,fields,fieldPermutations,nder,nfields,combinatoricsOfD},
nder=Exponent[term,der];
termaux=term/.der->1;
fields=(termaux/.Times->List/.Power->(Table[#,#2]&))//If[Head[#]=!=List,List[#],#]& //Flatten;
fieldPermutations=fields//Permutations;
nfields=Length[fields];

combinatoricsOfD=FrobeniusSolve[Table[1,nfields],nder];

Inner[ReverseApplied[DD],combinatoricsOfD,#,Dot]&/@fieldPermutations//Flatten
]

applyDerivativesAndPermutations::usage = "applyDerivativesAndPermutations[term_] returns all possible orderings of the fields in term, freezing the order with Dot. Also distributes the n derivatives (der^n) among them. Transforms notation as field -> DD[field,n]";


(* ::Subsubsection:: *)
(*Distribute traces*)


Clear[introduceTraces]
introduceTraces[terms_]:=Module[{aux=terms},
aux=\!\(\(applyDistributed[TR, #] &\)
\*SubscriptBox[\(/@\), \(2\)]aux\);
aux=aux//Map[Flatten]//Map[DeleteDuplicates];
aux=aux//sortTracesSimple;
aux=aux//Map[DeleteDuplicates]//Flatten
]

introduceTraces::usage = 
"introduceTraces[terms_] puts the fields inside traces TR[] in all possible groupings,
respecting their order. It transforms the terms as e.g.

DD[field1,n].DD[field2,n].DD[field3,n] -> TR[DD[field1,n],DD[field2,n]] TR[DD[field3,n]]

The input terms must be a List of Lists, and have as header Dot.
This function also removes some obvious duplicates to speed up next steps.";


Clear[applyDistributed]
applyDistributed[func_,x_]:=Module[{list=If[Head[x]===Dot,List@@x,List[x]],aux},
aux=Internal`PartitionRagged[list,#]&/@partitionSchemesForXElem[Length[list]];
aux=Apply[func,aux,{2}];
Times@@@aux(*Times: traces commute*)]

applyDistributed::usage = 
"applyDistributed[func_,x_] surrounds the fields in x=Dot[fields__] with the header func, in all possible combinations. Used to introduceTraces";


Clear[sortTracesSimple]
sortTracesSimple[expr_]:=expr/.TR[a__]:> cyclicSort[TR[a]];
sortTracesSimple::usage = "sortTracesSimple[expr_] will reorder the arguments inside all TR[] appearing in expr, with MMA default ordering";

Clear[cyclicSort]
cyclicSort[TR[]]:=TR[];
cyclicSort[TR[args__]]:=Module[{aux={args}},
If[CountDistinct[aux]==1,Return[TR@@aux],{}];
aux=RotateLeft[aux,Ordering[aux,1]-1];
(*first=last*)
If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}];
If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}];
If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}];
TR@@aux]

Clear[cyclicSortOLD]
cyclicSortOLD[TR[]]:=TR[];
cyclicSortOLD[TR[args__]]:=Module[{aux={args}},
aux=RotateLeft[aux,Ordering[aux,1]-1];
If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}]; 
(*it's ok if all elements are the same. Because ReplaceRepeated (//.) will see that it does not change anymore*)
TR@@aux]


Do[Do[
partitionSchemesForXElemInYGroups[X,Y]=Apply[Join,Permutations/@Select[IntegerPartitions[X],Length[#]==Y&]];
,{X,10}],{Y,10}]

(*identical to groupTR*)

Do[
partitionSchemesForXElem[X]=partitionSchemesForXElemInYGroups[X,#]&/@Range[1,X]//Join@@#&
, {X,10}]


(*test//introduceTraces//showLengthFlat//showTiming;*)


(* ::Subsection:: *)
(*Index business*)


(* ::Subsubsection::Closed:: *)
(*Create all index permutations*)


Clear[generateIndexOrderings]
generateIndexOrderings[epsilonIndices_,{}]:={epsilonIndices}
generateIndexOrderings[epsilonIndices_,pairIndices_/;Length[pairIndices]>=1]:=Module[{nPairs,nSingles,indexPermutations,positionPairs,newlist},

nPairs=Length[pairIndices];
nSingles=Length[epsilonIndices];

indexPermutations=Permutations[Join[pairIndices,pairIndices]]//Cases[#,{pairIndices[[1]],___}]&;
positionPairs=Subsets[Range[2*nPairs+nSingles],{2*nPairs}];

newlist=Table[{},{j,Length[positionPairs]},{i,Length[indexPermutations]}];

Do[
newlist[[kk]][[jj]]=epsilonIndices;
Do[newlist[[kk]][[jj]]=Insert[newlist[[kk]][[jj]],indexPermutations[[jj]][[ii]],positionPairs[[kk]][[ii]]],{ii,1,2*nPairs}],{kk,1,Length[positionPairs]},{jj,1,Length[indexPermutations]}];
Flatten[newlist,{1,2}]
]

generateIndexOrderings::usage = "generateIndexOrderings[epsilonIndices_List,pairIndices_List] returns all possible permutations of the indices. The epsilonIndices have a single instance per term (contracted to something external) and are kept in the order they are given. Instead, pairIndices appear twice per term (contracted) and they are are inserted in all possible ways between the epsilonIndices. In the resulting terms, the first pairIndex is always pairIndices[[1]] (dummy index)";



(* ::Subsubsection::Closed:: *)
(*Index place holders*)


Clear[insertIndexPlaceHolders]
insertIndexPlaceHolders[expr_]:= expr/.DD[field_,nder_]:>DD[field,nder][index[nder+nIndices[field]]]

insertIndexPlaceHolders::usage=
"insertIndexPlaceHolders[expr_] will insert place holders with the total number N of indices that are needed 
in each field. Transforms the notation as 
DD[field,nder] -> DD[field,nder][index[N]].
Needs to know how many indices are carried by each field. Define nIndices[field] beforehand in the configuration
(done automatically in the BB definition in the examples)";


(* ::Subsubsection:: *)
(*Insert one set of indices*)


Clear[insertOneIndexCombination]
insertOneIndexCombination[expr_,indices_List]:=Block[{aux,pos,indPerSlot,start,end,rule},
aux=expr//inactivePower;

(*find position of index[n] in expression*)
pos=Position[aux,index[_Integer]];

(*determine the first (start) and last (end) element of indices_List that goes in each place holder*)
indPerSlot=Extract[aux,pos]/.index[n_]:>n;
end=Accumulate[indPerSlot];
start=1+Drop[Insert[end,0,1],-1];

(*replace place holders by the indices*)
rule=Table[pos[[i]]->Sequence@@indices[[start[[i]];;end[[i]]]],{i,Length[pos]}];
ReplacePart[aux,rule]//Activate
]

insertOneIndexCombination::usage = "insertOneIndexCombination[expr_,indices_List] introduces n indices, in the notation specified in indices_List, in place of index[n], sequentally adds the rest of indices in all index[m].";


(* ::Subsubsection:: *)
(*Insert indices*)


(* ::Text:: *)
(*Assumes the existence mIndices and jIndices*)


Clear[insertIndices]

insertIndices[expr_]:=
If[Head[expr]===List, Map, Identity][
insertOneIndexCombination[expr,#]&/@indPerm[nbrOfIndices[expr]]
]

Clear[nbrOfIndices]
nbrOfIndices[expr_]:=Module[{aux,pos},
aux=expr//inactivePower;
Total[Cases[aux,index[n_]->n,99]]
]

Clear[indPerm]
indPerm[n_] := generateIndexOrderings[mIndices,jIndices[[1;;(n-Length[mIndices])/2]]]

(*term=F[a][index[7]]*G[b][index[3]]^2
nbrOfIndices[term]*)


insertIndices::usage = 
"insertIndices[expr_] will insert all possible sequences of indices in the places defined 
by //insertIndexPlaceHolders. The user must define which are the contracted jIndices, 
and which mIndices only appear once per operator (e.g. go with an external LeviCivita)

For example:
mIndices={m1,m2,m3,m4};
jIndices={j1,j2};

isM=MemberQ[mIndices,#]&;
isJ=MemberQ[jIndices,#]&;
";


(* ::Section::Closed:: *)
(*[Functions] Trivial relations*)


(* ::Subsection::Closed:: *)
(*sortTracesBare: order arguments in traces with MMA ordering*)


Clear[cyclicSortBare,sortTracesBare]
cyclicSortBare[TR[]]:=TR[];
(*cyclicSortBare[TR[args__]]:=RotateLeft[TR[args],Ordering[{args},1]-1]*)
cyclicSortBare[TR[args__]]:=Module[{aux={args}, extraRot},
aux=RotateLeft[aux,Ordering[aux,1]-1];

(*first = last. Only 2 identicals possible (2 j1s)*)
If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}]; 

(*Cases {a_,b__,a_,c__}*)
(*Length of b & c must be equal since this function is only to find symmetric cases*)
If[EvenQ[Length[aux]]&&MatchQ[aux,{a_,b__,a_,c__}],{},Return[TR@@aux]];
aux/.{a_,b__,a_,c__}:>If[Order[{b},{c}]==-1,aux=RotateLeft[aux,1+Length[{b}]],aux];

TR@@aux]

Clear[sortTracesBare]
sortTracesBare[expr_]:=expr/.TR[a__]:> cyclicSortBare[TR[a]];
(*TR[11,3,99,7]TR[b,a,c]//sortTracesBare*)


(* ::Subsection::Closed:: *)
(*ignoreSigns / addSigns / deleteDuplicatesSign: deal with signs*)


Clear[pullSign]
pullSign[expr_]:=expr//.TR[a___,sign x_,b___]:>sign TR[a,x,b]

(*sign TR[DD[fm,0][j1,m1],DD[fm,0][j2,j1],sign DD[fp,0][j2,m2],DD[u,1][m3,m4]]
%//pullSign*)


Clear[ignoreSigns]
ignoreSigns[expr_]:=expr/.sign->1


Clear[addSigns]
addSigns[expr_]:=expr/.sign->-1


Clear[simplifySign]
simplifySign[expr_]:=expr/.{sign^2->1,sign^3->sign,sign^4->1,sign^5->sign,sign^6->1,sign^7->sign}


(* ::Subsubsection::Closed:: *)
(*Delete signed duplicates*)


(* ::Text:: *)
(*We look at the sign of the first element. And if its negative, flip the sign of the whole expression with flipSigns.*)
(*Then DeleteDuplicates*)


Clear[deleteDuplicatesSign]
deleteDuplicatesSign[list_]:=Map[flipSigns,list]//DeleteDuplicates

Clear[flipSigns]
flipSigns[expr_Times]:= Module[{needsSign=False},
expr/.Times[_?Negative,z___]:>(needsSign=True;0);
If[needsSign,- expr, expr]
]
flipSigns[expr_Plus]:=Module[{needsSign=False},
expr/.Plus[x_,y___]:>
(x/.Times[_?Negative,z___]:>(needsSign=True;0));
If[needsSign,- expr, expr]
]
flipSigns[expr_?((Head[#]=!=Plus)&&(Head[#]=!=Times)&&(Head[#]=!=List)&)]:= expr
flipSigns[expr_List]:=Map[flipSigns,expr]

(*{a*b -c*d, -b*f,a*b+c*d,c*d-a*b}
%//deleteDuplicatesSign

-TR[DD[fm,0][m1,m2],DD[fp,1][j1,j2,m3],DD[u,0][j1],DD[u,1][j2,m4]]+TR[DD[fm,0][m1,m2],DD[fp,1][j1,j2,m3],DD[u,1][j2,j1],DD[u,0][m4]];
{%,%//flipSigns}//see*)


Clear[deleteDuplicatesSignBy]
deleteDuplicatesSignBy[F_][list_]:=Map[flipSigns,list]//DeleteDuplicatesBy[F]

Clear[deleteZeroesBy]
deleteZeroesBy[F_][list_]:=Module[{aux=list},
Do[
aux[[ii]]=If[F[aux[[ii]]]===0,0,aux[[ii]]]
,{ii,Length[aux]}];
aux//DeleteCases[0]
]



(* ::Subsection::Closed:: *)
(*Apply function on the terms*)


Clear[onTerms]
onTerms[F_][expr_]:=Distribute[Hold[F][Expand[expr]]]//ReleaseHold

(*TR[DD[chim,0][]] TR[DD[chip,0][]] TR[DD[fm,0][m1,m2],DD[u,1][m3,m4]]+8TR[DD[chim,1][m1]] TR[DD[chip,0][]] TR[DD[fm,0][m2,m3],DD[u,0][m4]];
{%,%//onTerms[APPLY]}//see*)

onTerms::usage = 
"onTerms[F_][expr_] will apply the function F on the operators themselves, expanding some simplifications beforehand.
It is not as effective as onTermsStrict, which actually ensures that F is applied only on the product of traces.";


Clear[onTermsStrict]
onTermsStrict[f_][expr_]:=Module[{aux=expr,TERM},

(*tag the TERMs without distracting factors/signs*)
TERM[n_?NumericQ x_]:=n TERM[x]; 
TERM[sign^a_ x_]:=sign^a TERM[x]; 
TERM[sign x_]:=sign TERM[x];
TERM[n__?(Head[#]=!=TR&& !MatchQ[#,Power[a_TR,2]]&)x_ y_. z_.]:=n TERM[x y z];

If[Head[expr]===List,
aux=aux//Map[onTerms[TERM]],
aux=aux//onTerms[TERM]]; 

aux/.TERM[a_]:>f[a]
]

onTerms::usage = 
"onTermsStrict[f_][expr_] will apply the function f strictly on the operators (composed of TR). ";


(* ::Subsection::Closed:: *)
(*getDictionaryOfShapes*)


Clear[getDictionaryOfShapes]
getDictionaryOfShapes[list_]:=list/.{first_,rest___}:>Map[#->first&,{first,rest}]/.(sign^p_. a_->b_):>(a->sign^p b)

getDictionaryOfShapes::usage = " getDictionaryOfShapes[list_] will create a set of replacement rules making all elements 
in the list be replaced by the first element. Replacement can be accelerated with Dispatch. 
It is intended for the following case:
When we have a list of lists, in which each sublist contains all the possible ways to write a term, then we can construct a 
dictionary (set of Rules accelerated with Dispatch) such that when any of the shapes is found anywhere it will automatically 
be rewritten as the first. Signs are ignored in these simple examples
";

Clear[landRulesOnZero]
landRulesOnZero[expr_]:= expr /. RuleDelayed[lhs_,rhs_]:>RuleDelayed[lhs,0] /. Rule[lhs_,rhs_]:>Rule[lhs,0]

Clear[rulesToFunctionOLD]
rulesToFunctionOLD[rules_List | rules_Dispatch][expr_] := onTermsStrict[ReplaceAll[#,rules]&][expr]

Clear[rulesToFunction]
rulesToFunction[rules_List | rules_Dispatch] := Module[{preDispatchedRules}, 
preDispatchedRules = rules//Dispatch;
Function[expr,expr//onTermsStrict[#/.preDispatchedRules &]]]

(*onTermsStrict is needed to use hash tables (Dispatch) with Times. It preselects the arguments of Times that the rule is applied on.
https://mathematica.stackexchange.com/questions/223744/dispatch-not-working-properly-with-times*)


(* ::Subsection::Closed:: *)
(*Identify terms; orderFields; getTraceScore*)


Clear[orderFields]
orderFields[expr_?(Head@Head@#===DD&)]:=expr/.DD[f_,n_][ind___]:>(Switch[f, fa,10+n, fb,20+n, fc,30+n])

orderFields::usage = "orderFields[expr_] is a user-defined function. It is the core function that defines the importance 
of each field in the terms. Other functions that directly or indirectly depend on it are:
 - general MINIBAR functions: getTraceScore, termScore, makeIdentifyTerms
 - user functions in the examples: standardizeShapes and functions within, identifyTerms";


(*define which trace goes first in the expression, before reintroducing m/j indices in order*)
Clear[getTraceScore]
getTraceScore[0]:=0;
getTraceScore[expr_]:=expr/.TR[args__]:>TR[Sequence@@(orderFields/@{args})]

getTraceScore::usage = "getTraceScore[expr_] converts every TR[a,b,c,...] into TR[x] where x is a number. 
Needs the user-defined function orderFields.";

Clear[termScore]
termScore[term_]:=Module[{aux},
aux=term//getTraceScore;
aux/.TR[seq__]:>(len=Length[{seq}];Total[{seq}*Prime[Range[len]]])]

termScore::usage = "termScore[term_] converts the term into a number accounting for the field content and the number
of arguments in the traces TR[arg__]. Needs the user-defined function orderFields (needed by getTraceScore).";

(*TR[DD[fa,0][k],DD[fb,0][k]] TR[DD[fc,0][k,k]];
{%,%//getTraceScore}//TableForm
{%%,%%//termScore}//TableForm
*)



Clear[makeIdentifyTerms]
makeIdentifyTerms[lag_,lagDictionary_,lagScores_][expr_]:=Module[{aux=expr,TERM,pos,termsWithSameScore},

(*tag the TERMs without distracting factors/signs*)
TERM[n_?NumericQ x_]:=n TERM[x]; 
TERM[sign^a_ x_]:=sign^a TERM[x]; 
TERM[sign x_]:=sign TERM[x];
TERM[n__?(Head[#]=!=TR&& !MatchQ[#,Power[a_TR,2]]&)x_ y_. z_.]:=n TERM[x y z];

aux=aux//Map[onTerms[TERM]]; 

(*subtitute TERM[a_] by ope[i], where i is the position of the term in 'lag'. 
Abort[] if some term is not identified, printing some likely candidates*)
aux/.TERM[a_]:>( 
pos=Lookup[lagDictionary,a];

If[NumericQ[pos[[1]]],{}, 

termsWithSameScore=Position[lagScores,termScore[a]]//Flatten;
Print[" Term not identified: \n",a//readableNotation,"\n Candidates: \n" ,lag[[termsWithSameScore]]//readableNotation];
Print[" In ugly notation : \n",a,"\n Candidates in ugly: \n" ,lag[[termsWithSameScore]]];
Abort[];
];

ope[pos[[1]]]
)
];

makeIdentifyTerms::usage = "makeIdentifyTerms[lag_,lagDictionary_,lagScores_][expr_] takes the
INPUTS:
lag - a list of terms
lagDictionary=PositionIndex[lag]; 
lagScores=lag//Map[termScore]; - the user must define orderFields, which automatically defines getTraceScore, and this termScore. 

OUTPUTS:
Retuns a pure function that we will call it identifyTerms[expr_] in the workflow of the calculation. This is able
to separate and identify the terms of our basis 'lag' appearing in any expression, and then substitute them by
ope[i], where i is the position of the term in the list 'lag'. See the usage of identifyTerms in the calculation examples";


(* ::Section::Closed:: *)
(*[Functions] Operator relations*)


(* ::Subsection::Closed:: *)
(*Tidy up relations: removeOverallFactor, relWithIntegers, cleanTraces*)


Clear[removeOverallFactor]
removeOverallFactor[expr_]:=expr//FactorTerms//Replace[#,Times[_?NumericQ,rest_]:>rest]&

Clear[removeOverallFactorReal]
removeOverallFactorReal[expr_]:=expr//FactorTerms//Replace[#,Times[f_?(#\[Element]Reals &),rest_]:>rest]& //Replace[#,Times[f:Complex[a_,b_?(#!=0&)] , rest_]:>(f/b)rest ]&

Clear[rmOverallReal]
rmOverallReal[list_]:=Map[(#//Factor//Replace[Times[a_?realQ , b__]:>Times[b]]//Replace[Times[a:Complex[A_,B_],b__]:>(1/B)*Times[a,b]]//Expand)& ,list];

ClearAll@realQ
SetAttributes[realQ, Listable]
realQ[_Real | _Integer | _Rational] := True
realQ[Pi] := True
realQ[Complex[_, 0.]] := True
realQ[Complex[_, _?(#=!=0&)]] := False
realQ[x_] := NumericQ[x]

(*realQ[{"text", 0, 3.0, 1/2, 2*I, Pi, 1 + 0. I}]*)

removeOverallFactor::usage = 
"removeOverallFactor[expr_] removes any numeric (including Complex) overall factor from the expr";

removeOverallFactorReal::usage = 
"removeOverallFactorReal[expr_] removes the real overall factor, or if it is complex, leaves the imaginary part = 1 (so =i).

rmOverallReal should do the same";

rmOverallReal::usage = 
"rmOverallReal[expr_] very similar to removeOverallFactorReal";


(*Homemade version*)
Clear[relWithIntegers]
relWithIntegers[expr_]:=Module[{aux,maxFactor},
aux=Cases[expr,Rational[_,n_]:>n,99];
If[aux==={},Return[expr],{}];
maxFactor=Max[aux];
maxFactor*expr//Distribute
]



Clear[cleanTracesOLD]
cleanTracesOLD[expr_]:=Module[{aux=expr},
aux=aux/.TR[A___]:>Map[Expand,TR[A]];
aux=aux//.TR[A___,a_+b_+c_,B___]:>TR[A,a,B]+TR[A,b,B]+TR[A,c,B];
aux=aux//.TR[A___,a_+b_,B___]:>TR[A,a,B]+TR[A,b,B];
aux=aux//.TR[A___,a_+2 b_,B___]:>TR[A,a,B]+2 TR[A,b,B];
aux=aux//.TR[A___,a_TR,B__]:>a TR[A,B]; (*A can be empty, not B*)
aux=aux//.TR[A__,a_TR,B___]:>a TR[A,B]; (*viceversa*)
aux=aux//.TR[TR[a__]]:>Nf TR[a]; (*Both empty: Nf factor*)
aux=aux//.TR[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)DD[x__] [y___],B___]:>n TR[A,DD[x][y],B];
aux=aux//.TR[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)seq[x__],B___]:>n TR[A,seq[x],B];
aux=aux//.TR[A___,seq[x__],B___]:>TR[A,Sequence[x],B];
aux=aux//.TR[A___,{x__},B___]:>TR[A,Sequence[x],B]

]

Clear[cleanTraces]
cleanTraces[expr_]:=Module[{aux=expr,tr},

(*Define rules for tr*)
tr[A___,a_Plus,B___]:=(tr[A,#,B]&)/@a ;
tr[A___,n_?NumericQ x_,B___]:=n tr[A,x,B];
tr[A___,a_tr,B__]:=a tr[A,B]; (*A can be empty, not B*)
tr[A__,a_tr,B___]:=a tr[A,B]; (*viceversa*)
tr[tr[a__]]:=Nf tr[a]; (*Both empty: Nf factor*)
tr[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)DD[x__] [y___],B___]:=n tr[A,DD[x][y],B];
tr[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)seq[x__],B___]:=n tr[A,seq[x],B];
tr[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)tr[x__],B___]:=n tr[A,tr[x],B];
tr[A___,seq[x__],B___]:=tr[A,Sequence[x],B];
tr[A___,{x__},B___]:=tr[A,Sequence[x],B];

aux=aux/.TR[A___]:>Map[Expand,TR[A]];
aux=aux/.TR:>tr;

aux=Evaluate[aux];
aux=aux/.tr->TR

]

cleanTraces::usage =
"cleanTraces[expr_] distributes the sums of matrices within the traces; pulls out numerical factors; ungroups matrices either with 
seq[A,B] or curly brackets {A,B}; pulls out TR[TR[A],B] = TR[A] TR[B]; and writes TR[1] = Nf.

In summary, it cleans the traces. Used by getRelationsFromRule.";


(* ::Subsection::Closed:: *)
(*checkRule: check user-defined identities*)


Clear[checkRule]
checkRule[tag_,rule_]:=Module[{},
If[(rule[[1]]/.tagX:>firstHead[tag[dummy][[1]]])=!=(tag[dummy][[1]]//removeDollarSign), 
Print["WARNING: tag and rule should have identical LHS except for the headers: tagX and DD"]];
(rule[[1]]/.tagX->firstHead[tag[dummy][[1]]]//removePatterns) -> ((rule[[1]]//removePatterns) /.rule )//see
]

checkRule[rule_]:=Module[{},
(rule[[1]]//removePatterns) -> ((rule[[1]]//removePatterns) /.rule )//see
]

Clear[firstHead]
firstHead[expr__] := If[Length[{expr}]>1,seq,firstHead[expr]]
firstHead[expr_] := If[Length[{expr}]>1,seq,NestList[Head,expr,5]//#[[FirstPosition[#,Symbol][[1]]-1]]&]

checkRule::usage =
"checkRule[rule_] prints the rule nicely formatted to help in its writing.

Internally, it removePatterns in the LHS to print the rule, so it assumes the lowest possible match. 
In practice: to work on DD[field_,n_][i1_,i2_], n_ must have a test like n_?(#>=0&) 

-----

(DEPRECATED) TWO ARGUMENTS VERSION

checkRule[tag_,rule_] checks that the tag will only be placed on the terms where the rule applies. 
It also prints the rule nicely formatted to help in its writing";

firstHead::usage = 
"firstHead[expr_] will return the foremost Head of the expression. It is different than Head as
DD[field,n][ind] // Head = DD[field,n]
while
DD[field,n][ind] // firstHead = DD";


Clear[removeDollarSign]
removeDollarSign[expr_]:=expr//FullForm//ToString//StringReplace["$"->""]//ToExpression

Clear[removePatterns]
removePatterns[expr_] := expr /.
Verbatim[Pattern][_,Verbatim[BlankNullSequence][]]:>Sequence[] /.
Verbatim[PatternTest][sym_,test_]:>(k=0;While[!test[k] && k!=99,k++];
If[k==99, Print["ERROR: Sorry, I can't check. Your PatternTest is too complicated for me"];Abort[]];k) /. 
Verbatim[Pattern][sym_,___]:>sym

removePatterns::usage = 
"removePatterns[expr_] will replace the patterns in the expression by their symbol (i.e. A_ -> A).
Blank (_) and BlankSequence (__) are replaced by the symbol, whereas BlankNullSequence (___) is directly removed.

This is used by checkRule to print the rule in a nice readable format, but will fail if the number of derivatives n
in DD[field_,n_][ind__] does not have a Patterntest attached like n_?(#>1&).
";


(* ::Subsection::Closed:: *)
(*getRelationsFromRule: find operator relations from user-defined identities*)


(* ::Text:: *)
(*This function finds all ocurrences of tag in each term, and duplicates the term as many times as necessary to have only one insertion of the rule in each place.*)


Clear[getRelationsFromRule]

getRelationsFromRule[lag_List, rule_, maxOcurrences_: 3] := Module[{head, tag, ruleX, tagRHS, tagLHS, lagTagged, allInsertions, tmpLag},

(*Head of the rule: typically DD or TR*)
head = rule[[1]] // firstHead;

(*Create ruleX: tagX -> rule*)
ruleX = rule;
ruleX[[1]] = ruleX[[1]] /. head -> tagX;

(*Create tag function from rule, to tag ocurrences*)
tagLHS = rule[[1]] // Evaluate;
tagRHS = (Evaluate[(rule[[1]] /; i++ < 1) /. Verbatim[Pattern][name_, _] :> name /. Verbatim[PatternTest][name_, _] :> name]);
tag[XX_] := tagLHS :> Evaluate[(tagRHS /. head -> XX)];

(*Tag ocurrences with tagX*)
lagTagged = lag;
Do[tmpLag = lagTagged; lagTagged = Map[(i=0; # /. tag[case[iii]])&, tmpLag], {iii, maxOcurrences}];
lagTagged = Join @@ Table[lagTagged /. {case[iii] -> tagX}, {iii, maxOcurrences}];
lagTagged = Select[lagTagged, !FreeQ[#, tagX[__]]&];
lagTagged = lagTagged /. case[_] -> head;

(*Apply ruleX*)
allInsertions = lagTagged /. ruleX // Flatten;
Print[allInsertions // Length, " relations found"];
allInsertions // cleanTraces // Map[Distribute]
]

(*getRelationsFromRule[lag_List, rule_, maxOcurrences_:3] := Module[{head, tag, ruleX, tagRHS, tagLHS, lagTagged, allInsertions, tmpLag},
        (*Head of the rule: typically DD or TR*)
        head = rule[[1]] // firstHead;
        (*Create ruleX: tagX -> rule*)
        ruleX = rule;
        ruleX[[1]] = ruleX[[1]] /. head -> tagX;
        (*Create tag function from rule, to tag ocurrences*)
        tagLHS = rule[[1]] // Evaluate;
        tagRHS = (Evaluate[(rule[[1]] /; i++ < 1) /. Verbatim[Pattern
            ][name_, _] :> name /. Verbatim[PatternTest][name_, _] :> name]);
        tag[XX_] := tagLHS :> Evaluate[(tagRHS /. head -> XX)];

(*Tag ocurrences with tagX*)
        lagTagged = lag;
        Do[tmpLag = lagTagged; lagTagged = Map[(i = 0; # /. tag[case[
            iii]])&, tmpLag], {iii, maxOcurrences}];
        lagTagged = Join @@ Table[lagTagged /. {case[iii] -> tagX}, {
            iii, maxOcurrences}];
        lagTagged = Select[lagTagged, !FreeQ[#, tagX[__]]&];
        lagTagged = lagTagged /. case[_] -> head;
        (*Apply ruleX*)
        allInsertions = lagTagged /. ruleX // Flatten;
        Print[allInsertions // Length, " relations found"];
        allInsertions//cleanTraces // Map[Distribute]
    ]*)


getRelationsFromRule::usage = 
"getRelationsFromRule[lag_List, rule_, maxOcurrences_:3] builds operator combinations that vanish according to the
identity encoded in rule. The LHS of rule is the entry point to insert the identity in the operators of lag. The
RHS contains a combination that vanishes.

For example: given the identity f[A]+g[B]+f[C]=0, we should write rule = (f[A] :> f[A]+g[B]+f[C]). 

If f[A] may be zero, it is safer to insert the relation through all terms: call getRelationsFromRule 3 times with
rule1 = (f[A] :> f[A]+g[B]+f[C]);
rule2 = (g[B] :> f[A]+g[B]+f[C]);
rule3 = (f[C] :> f[A]+g[B]+f[C]);

The 3rd argument is OPTIONAL: maxOcurrences defines how many times the LHS of rule may appear in a single operator.
Set it higher to be safe. Lower to speed things up.

If the LHS of rule appears at most once in each term, these two approaches are equivalent:
Complement[lag/.rule,lag]
getRelationsFromRule[lag,rule]

Otherwise, the rule must be inserted one at a time, in each of the ocurrences: that's what this function is for.

----------------

(DEPRECATED) VERSION WITH 4 ARGUMENTS

getRelationsFromRule[lag_List,rule_,tag_,head_]

 - rule econdes the identity. If f[A]+f[B]+f[C]=0, we should write rule = (tagX[A] -> f[A]+f[B]+f[C]). 
If some of the terms involved in the identity may be zero in some cases because of index antisymmetries, 
it is safer to insert the relation through all terms. Call again getRelationsFromRule, now with 
rule = (tagX[B] -> f[A]+f[B]+f[C])

 - tag encodes the LHS of rule. The tag must include at the end '/; i++<1'. In the examples above, 
it should be tag = (tagFunction[tag_] := f[A]->tag[A]/; i++<1)

 - head is the Head of the LHS of rule (usually TR or DD). In the example above head = f

check that tag and rule are compatible with checkRule
";

(*lagFMU = lag // findWithNDer[u, 1] // findExact[u, u, u, u];
getRelationsFromRuleNEW[lagFMU[[1 ;; 2]], ruleFMUtn] // showTiming // see;
getRelationsFromRuleNEW[lag[[1 ;; 750]], ruleBItn] // showTiming // see;
*)

(*ruleTEST=tagX[u,n_][ind___,a_,a_]:>DD[u,n][ind,a,a] -(1/2)ii DD[chim,n-1][ind]+TR[(1/Nf)ii DD[chim,n-1][ind]];
tagTEST[DDtag_]:=DD[u,n_][ind___,a_,a_]:>DDtag[u,n][ind,a,a] /;i++<1;

fullTEST=getRelationsFromRule[lag[[1;;1000]],ruleTEST,tagTEST,DD]//showTiming;
%//see*)


(*(PREVIOUS) VERSION WITH 4 ARGUMENTS*)

getRelationsFromRule[lag_List,rule_,tag_,head_]:=Module[{lagTagged,allInsertions,tmpLag},
lagTagged=ConstantArray[0,Length[lag]];

tmpLag=lag;
lagTagged=Map[(i=0;#/.tag[tag1])&,tmpLag]; 

tmpLag=lagTagged;
lagTagged=Map[(i=0;#/.tag[tag2])&,tmpLag]; 

tmpLag=lagTagged;
lagTagged=Map[(i=0;#/.tag[tag3])&,tmpLag]; 

lagTagged=Join[
lagTagged/.{tag1->tagX,tag2->head,tag3->head},
lagTagged/.{tag1->head,tag2->tagX,tag3->head},
lagTagged/.{tag1->head,tag2->head,tag3->tagX}];

lagTagged=Select[lagTagged,!FreeQ[#,tagX[__]]&];

allInsertions=lagTagged/.rule//Flatten;
Print[allInsertions//Length, " relations found"];
allInsertions//cleanTraces//Map[Distribute]

]


(*ruleTEST=DD[u,n_][ind___,a_,a_]:>DD[u,n][ind,a,a] -(1/2)ii DD[chim,n-1][ind]+TR[(1/Nf)ii DD[chim,n-1][ind]];
fullTEST=getRelationsFromRule[lag[[1;;1000]],ruleTEST]//showTiming//see;*)


(* ::Subsubsection::Closed:: *)
(*Keeping a previous version*)


(* ::Subsubsubsection::Closed:: *)
(*Faster getRelationsFromRuleFast (Not always useful)*)


(* ::Text:: *)
(*The bottleneck is in cleanTraces, so this (simpler) code improves the overall speed only by 20%. But cannot be used for head !=DD*)


(*Clear[getRelationsFromRuleFast]
getRelationsFromRuleFast[lag_List,rule_,tag_,_]:=Module[{lagTagged,allInsertions,newtag},

(*Remove rule conditions and newtag = lhs+a*rhs*)
newtag = tag[tagX]/.(RuleDelayed[lhs_,Verbatim[Condition][rhs_,_]]):>RuleDelayed[lhs,rhs];
newtag = newtag/.RuleDelayed[lhs_,rhs_]->RuleDelayed[x:lhs,x+a*rhs];

lagTagged=lag/.newtag;
lagTagged=(lagTagged)//.TR[A___,x_+a*y_,B___]:> TR[A,x,B] + a TR[A,y,B]//Expand;
lagTagged=lagTagged//Map[Coefficient[#,a,1]&]//Map[plusToList]//Flatten;

allInsertions=lagTagged/.rule//Flatten//DeleteCases[0];
Print[allInsertions//Length, " relations found"];
allInsertions//cleanTraces//Map[Distribute]
]

ruleFMUt=tagX[fm,n_?(#==0&)][ind___,a_,b_]:>DD[u,n+1][ind,a,b] - DD[u,n+1][ind,b,a]+DD[fm,n][ind,a,b];
tagFMUtc[tag_]:=DD[fm,n_?(#==0&)][ind___,a_,b_]:>tag[fm,n][ind,a,b]/;i++<1 ;
tagFMUt[tag_]:=DD[fm,n_?(#==0&)][ind___,a_,b_]:>tag[fm,n][ind,a,b];
*)


(*getRelationsFromRule[lag[[1;;2]],ruleFMUt,tagFMUtc,DD]//showTiming;
getRelationsFromRuleFast[lag[[1;;2]],ruleFMUt,tagFMUtc,DD]//showTiming;*)


(* ::Subsection::Closed:: *)
(*rotateTraces: generate all orderings of the traces *)


Clear[rotateTraces]
rotateTraces[lag_]:=Module[{rotatedlag=ConstantArray[0,8],newlag},
Do[
rotatedlag[[nrot]]=lag/.TR[arg__]:>TR[Sequence@@RotateLeft[{arg},nrot]]/;Length[{arg}]>nrot;
,{nrot, 8}];

newlag=rotatedlag//Flatten//DeleteDuplicates;
Print["Expanded basis with all rotations of the traces: ", Length[lag], " \[RightArrow] ",Length[newlag], " terms"];
newlag
]

(*rotateTraces[lag];*)

rotateTraces::usage = 
"rotateTraces[lag_] will expand the list of operators in lag, writing explicitly all the cyclic rotations of
the traces TR. This is useful to consider all possible matrix products within the traces in some of the operator
relations.";


(* ::Subsection::Closed:: *)
(*Helpers to debug - findLinearlyDependent, findSameOperators*)


Clear[justOpes,findLinearlyDependent,findSameOperators]
justOpes[expr_]:=(expr//plusToList)//.x_. ope[xx_]:>ope[xx]/.- ope[a_]->ope[a];
findLinearlyDependent[list_]:= Gather[list,IntersectingQ[#1//justOpes,#2//justOpes]&]//Cases[{_,__}];
findSameOperators[list_]:=GroupBy[list,#//.x_. ope[xx_]:>ope[xx] //.x_. ope[xx_] + y_. ope[yy_]:>ope[xx*yy ]&]//Cases[{_,__}];


(*{{ope[1601]+ope[1656]+ope[1722]+ope[1723],ope[1601]+ope[1656]-ope[1722]-ope[1723]},{ 1/2 ii ope[1601]-ope[10241]+ope[10243]+ope[10532]+ope[10533],ope[10239]-ope[10241]+ope[10243]-ope[10532]-ope[10533]},{ope[11901]-ope[11903]+ope[11905]+ope[12194]+ope[12195],ope[11901]-ope[11903]+ope[11905]-ope[12194]-ope[12195]}};
%//Flatten;
%//findSameOperators//TableForm
%%//findLinearlyDependent//TableForm*)


(* ::Subsection::Closed:: *)
(*Cayley-Hamilton [CH]*)


(* ::Text:: *)
(*Helper functions to extract operator relations from Cayley-Hamilton trace relations*)
(**)
(*Group the arguments of each TR into nf Lists in all possible ways. Allow also any leftover arguments at the end.*)


Clear[separateArgsTR]
separateArgsTR[nf_][terms_]:=Module[{listArgs,npart},
terms/.TR[a___]:>(listArgs={a};
If[Length[listArgs]<nf,
TR[a],
Total[TR@@@Join[
Internal`PartitionRagged[listArgs,#]&/@groupTR[Length[listArgs],nf],
Internal`PartitionRagged[listArgs,#]&/@groupTR[Length[listArgs],nf+1]//Map[#/.{first__,last_}:>{first,Sequence@@last}&]
]]]
)//Expand//ReplaceAll[Plus->List]
]


(*TR[a,b,c,d]TR[G,H]//separateArgsTR[3]//TableForm*)


separateArgsTR::usage = 
"separateArgsTR[nf_][terms_] groups the matrices inside the traces TR in all possible ways.
It creates nf groups, surrounded by curly brackests (List[]) and possibly some leftover matrices at the end of the trace.
To account for the cyclicity of traces in these grouping schemes, use rotateTraces before";


(* ::Text:: *)
(*Pre-calculate grouping schemes for a list of length len and npart subgroups. Store results in the symbols groupTR[len,npart]*)
(*groupTR = partitionSchemesForXElemInYGroups*)


Do[Do[
groupTR[len,npart]=Apply[Join,Permutations/@Select[IntegerPartitions[len],Length[#]==npart&]];
,{len,8}],{npart,8}]


(* ::Text:: *)
(*Function to sort the matrices inside a group to avoid creating duplicate relations*)


Clear[sortGroupsCH]
sortGroupsCH[termsWithGroupedTR_]:=termsWithGroupedTR/.TR[arg__List]:>TR[Sequence@@Sort[{arg}]]/.TR[arg__List,leftover__?(Head[#]=!=List&)]:>TR[Sequence@@Sort[{arg}],leftover]

sortGroupsCH::usage = 
"sortGroupsCH[termsWithGroupedTR_] will re-order the groups of matrices in the traces TR like

TR[{B,B,C},{A,A},D] -> TR[{A,A},{B,B,C},D]

This is useful to remove redundant terms that would lead to the same Cayley-Hamilton trace relation.
";


(* ::Text:: *)
(*Get CH rule for any Nf*)


Clear[getRuleCayleyHamilton]
getRuleCayleyHamilton[NN_]:=Module[{logExpand,characPoly,simpleCH,aux,RHS,LHS,matAtoLetters,tr,cleanTracesCH,ruleCH,listMat,PEAK},


PEAK[expr_]:=expr//EchoFunction[(#/.tr->TR//plusToList//TableForm)&];


(*HELPERS*)
cleanTracesCH[expr_]:=expr//.
tr[A___,a_Plus,B___]:>(tr[A,#,B]&/@a)//.
tr[A___,a[n_] x_,B___]:>a[n]tr[A,x,B]//.
tr[A___,Times[-1,x__],B___]:>-tr[A,Times[x],B]//.
tr[A___, n_?NumericQ x_,B__]:>n tr[A,x,B]//.
tr[A___,a_*Power[b_tr,n_],B___]:>tr[A,a,b,B]//.
tr[A___,Power[b_tr,n_],B___]:>tr[A,Sequence@@ConstantArray[b,n],B]//.
tr[A___,a_*b__,B___]:>tr[A,a,b,B];

tr[a_Plus]:=tr /@ a;
tr[x_ A^n_]:=x tr[A^n];
tr[x_ A]:=x tr[A];

matAtoLetters[expr_]:=Module[{nB},
nB="B"//ToCharacterCode//First;
expr/.A[n_] :> (((n+nB-1)//FromCharacterCode)/."E"->"EE"/."I"->"II"/. s_String :> ToExpression[s])
];


(*OBTAIN RULE*)
(*CH relation for A*)
logExpand=Series[Log[1-(A/lam)],{lam,Infinity,NN+5}]//Normal;
characPoly=Series[lam^NN * Exp[tr[logExpand]],{lam,Infinity,NN+5}]//Normal//Expand;
simpleCH=characPoly/.lam^n_?Negative:>0/.lam->A;

(*Transform CH for A=B+C+D+...*)
aux=simpleCH//.tr[M_^n_]:>tr@@ConstantArray[M,n];
aux=aux/.A^n_:>Dot@@ConstantArray[A,n];
aux=aux/.A->Inner[Times,a/@Range[NN],A/@Range[NN],Plus]//cleanTracesCH;
aux=aux//.Dot[AA___,x_+y_,BB___]:>Dot[AA,x,BB]+Dot[AA,y,BB]//.Dot[AA___,a[n_]*A[m_],BB___]:>a[n]*Dot[AA,A[m],BB]//ExpandAll;
aux=aux/.a[_]^n_?(#>=2&):>0/.a[_]:>1;
aux=aux/.tr[A__]:>(tr[A]//RotateLeft[#,Ordering[#,1]-1]&);
aux=aux/.Nf->NN;

(*Write rule*)
RHS=aux//matAtoLetters//tr[#,Z]&;
RHS=RHS//cleanTracesCH;
RHS=RHS/.Dot:>Sequence//cleanTracesCH;
RHS=RHS/.tr->TR;
listMat=A/@Range[NN]//matAtoLetters;
LHS=({Pattern[#,BlankSequence[]]}& /@(TR@@listMat))//Append[Z___];

ruleCH=LHS:>Evaluate[RHS]
]

getRuleCayleyHamilton::usage = 
"getRuleCayleyHamilton[NN_] returns the replacement rule to find the Cayley Hamilton trace relation of NN x NN matrices, in the shape

TR[{B__},{C__},Z___]:> TR[B,C,Z] + ...

The brackets represent any group of matrices within the traces, which must be computed beforehand with separateArgsTR
";


(* ::Text:: *)
(*Wrapper function*)


Clear[getCayleyHamilton]
getCayleyHamilton[NN_][terms_List]:=Module[{termsSeparated,rule},

termsSeparated=terms//rotateTraces//separateArgsTR[NN]//Flatten//sortGroupsCH//DeleteDuplicates;
rule=getRuleCayleyHamilton[NN];
rel=getRelationsFromRule[termsSeparated,rule]/.Nf->NN;

(*Simplify a bit in simple cases*)
If[Length[terms]<100,
Print["Simplifying traces..."]; 
rel = rel//sortTracesBare//DeleteCases[0]//DeleteDuplicates; 
Print[Length[rel]," relations found"]];

rel

]

getCayleyHamilton[NN_][terms_?(Head[#]=!=List&)]:=getCayleyHamilton[NN][{terms}]

getCayleyHamilton::usage = 
"getCayleyHamilton[NN_][terms_] computes the Cayley Hamilton trace relations for the terms, which traces TR contain NN x NN matrices

TR[A,B,C] TR[A] TR[B] // getCayleyHamilton[2]

The returned linear combinations are equal to zero.
";


(* ::Subsection::Closed:: *)
(*Total derivatives [TD]*)


(* ::Text:: *)
(*Apply total derivative with x index and distribute with derivative of the product*)


Clear[Dx]
Dx[expr_]:=Module[{aux=expr,posField,fieldDx},
aux=aux/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);
posField=Position[aux,DD[_,_][___]];

Plus@@Table[
fieldDx=Extract[aux,posField[[i]]]/.DD[f_,n_][ind___]:>DD[f,n+1][x,ind];
ReplacePart[aux,posField[[i]]:>fieldDx]
,{i,Length[posField]}]//Activate
]

(*TR[DD[chip,0][],DD[fm,0][a,b],DD[fp,0][c,d]];
TR[DD[fm,0][a,b]] TR[DD[u,0][c]] TR[DD[u,0][d],DD[u,0][e],DD[u,0][f]];
{%,%//Dx}//see*)


(* ::Text:: *)
(*Substitute indices names (used for re-building the terms for TD relations)*)


Clear[subsIndices]
subsIndices[expr_,indPerm4_,indPerm6_,indPerm8_]:=Module[{nIndices},
nIndices=Which[!FreeQ[expr,g],8,!FreeQ[expr,e],6,!FreeQ[expr,c],4,!FreeQ[expr,a],2];
Switch[nIndices,
2,expr/.subsInd2,
4,expr/.subsInd4,
6,expr/.subsInd6,
8,expr/.subsInd8
]
]


(* ::Subsection::Closed:: *)
(*Schouten [SCH]*)


(* ::Text:: *)
(*To find Schouten-identity relations we identify the positions of the indices in each term and reintroduce the indices permuted. It is enough to account for 4 Levi-Civita indices and 1 of the pair indices. We define a specific function to do this:*)


Clear[getSchouten4m]
getSchouten4m[term_]:=Module[{aux=term,posM,posJ,pos5,ind5},

aux=aux/.Times:>Inactive[Times];
aux=aux/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);

posM=Position[aux,_?isM];
posJ=Position[aux,_?isJ];

pos5=Table[Join[posM,{posJ[[k]]}],{k,Length[posJ]}];
ind5=Table[Extract[aux,pos5[[k]]],{k,Length[posJ]}];

Table[
Total@Table[
ReplacePart[aux,MapThread[Rule,{pos5[[j]],RotateRight[ind5[[j]],k]}]],
{k,5}]
,
{j,Length[posJ]}]//Activate
]

getSchouten4m::usage = 
"getSchouten4m[term_] builds Schouten index relations for the terms. These ensure that when the indices can take up to D different values,
there cannot be a fully antisymmetric expression on more than D indices (because at least two of them would be identical, i.e. symmetric).

In this case, the antisymmetric index combinations are built with 5 indices: 4 LeviCivita indices (4m) and one contracted index (j). 
In principle one could have 3m + 2j, but these were proven to be linearly dependent to 4m + 1j relations.

The returned linear combinations are equal to zero.";


(* ::Section::Closed:: *)
(*[Functions] Transform and reorder terms*)


(* ::Subsection::Closed:: *)
(*Symmetrize terms*)


(* ::Text:: *)
(*Create linear combinations of terms such that they are eigenvectors under some discrete symmetries*)


Clear[symmetrize]
symmetrize[applyH_,applySym__][basis_]:=Module[
{termsTrans,terms,sym,symCH,HsymC,signsC,signsH,oddHGetsI,combinedOldOpes,opesCE},

(*Create sane combinations under all symmetries in applySym*)
terms=basis;
Do[
termsTrans=applySymLoop[terms];
terms=Join[terms+termsTrans,terms-termsTrans]//DeleteCases[0]//Map[removeOverallFactor]//addSigns//deleteDuplicatesSign;
, {applySymLoop,{applySym}}
];

(*Create sane combinations under applyH*)
termsTrans=applyH[terms];
terms=Join[terms+I termsTrans,terms-I termsTrans]//DeleteCases[0]//Map[removeOverallFactor]//addSigns//deleteDuplicatesSign;

If[Length[terms]=!=Length[basis], 
Print["ERROR: The number of terms before and after the transformation is not the same. Did you provide a complete basis? 
Otherwise your symmetries may be too complicated for this function (symmetrize). "]];


(*Correct odd H*)
(*If the eigenvalue of H is -1, I or -I; we must correct the term to make it be 1*)
signsH=((applyH[terms])/terms)//Simplify;
oddHGetsI=signsH/.{-1:>I,I:>(1+I),-I:>(1-I)};
terms=terms*oddHGetsI
]

symmetrize::usage = 
"symmetrize[applyH_,applySym__][basis_] will create combinations of terms in the basis such that they are eigenvectors 
under the discrete symmetries defined in applySym. The resulting combinations are Hermitian, which transformation is 
defined in the first argument, applyH.

The user-defined input transformations, besides applying the discrete symmetries, should leave the terms in the standard shape";


Clear[signsUnder]
signsUnder[applySym_][terms_] :=Module[{signs},
signs=(applySym[terms]/terms)//addSigns//Simplify;
(*CHECK that only has 1 or -1. Issue warning saying that we found eigenvalues equal to (_?NumericQ)*)
signs=signs//Map[Replace[_?(!NumericQ[#]&)->"NOT EIGENVECTOR"]];
signs
]

Clear[separateEvenOddUnder]
separateEvenOddUnder[applySym__][transformSymToRaw_,raw_]:= Module[{newOpes,signs,even,odd,terms},
newOpes=transformSymToRaw//Map[First];
terms=(transformSymToRaw//Map[Last])/.ope[n_]:>raw[[n]];
signs=Times@@((terms//signsUnder[#])/.-1:>0& /@ {applySym});

even = newOpes * (signs/.-1:>0) //DeleteCases[0];
odd = Complement[newOpes,even];

{even,odd}
]

Clear[separateEvenOddUnderOLD]
separateEvenOddUnderOLD[applySym_][transformSymToRaw_,raw_]:= Module[{newOpes,signs,even,odd,terms},
newOpes=transformSymToRaw//Map[First];
terms=(transformSymToRaw//Map[Last])/.ope[n_]:>raw[[n]];
signs=terms//signsUnder[applySym];

even = newOpes * (signs/.-1:>0) //DeleteCases[0];
odd = Complement[newOpes,even];

{even,odd}
]


signsUnder::usage = 
"signsUnder[applySym_][terms_] returns the eigenvalue of each term under the discrete symmetry applySym.";

separateEvenOddUnder::usage = 
"separateEvenOddUnder[applySym__][transformSymToRaw_,raw_] returns two lists of ope numbers with the even and odd 
operators under applySym. Even operators are even under each transformation separately. E.g. for applySym[P,C][...] 
the returned list of even operators does NOT contain terms with P=-1 and C=-1 (even for composite PC).

These opes are in the 'sym' basis. The input transformSymToRaw contains the set of rules to transform opes from the 
'sym' to the 'raw' basis and raw contains the terms of the raw basis themselves.";


Clear[simpleConjugate]
simpleConjugate[expr_]:=expr/.Complex[a_,b_]->Complex[a,-b]

simpleConjugate::usage = 
"simpleConjugate[expr_] flips sign of the imaginary part of the (explicit) Complex numbers in expr.";


getTransformationRules[combinedOldOpes_]:=Module[{newOpes,counters,counter,initialValues,list,transformation},

(*Create rules to transform newOpe \[Rule] combinedOldOpes. The newOpe number is always equal to one of the oldOpes.
This is necessary to use getInverseTransformation later*)

(*Get the list of newOpes without duplicates*)
list=combinedOldOpes//Map[Cases[#,ope[n_]:>n,{0,Infinity}]&]//Map[ope@@#&];
counters = Map[counter@@#&,list];
initialValues = Thread[counters -> 1];
Set @@@ initialValues;
newOpes=list/.ope[args__]:>ope[{args}[[counter[args]++]]];

(*Output*)
transformation=MapThread[Rule,{newOpes, combinedOldOpes}]

]

getTransformationRules::usage = 
"getTransformationRules[combinedOldOpes_] returns a list of rules for the transformation of terms from the 
new basis into the old one. The new basis is formed with combinations of operators in the old basis (combinedOldOpes).
The numbering is kept in the transformations. Example:

combinedOldOpes={ope[1]+ope[2], ope[3],ope[1]-ope[2]}

Output: {ope[1]->ope[1]+ope[2], ope[3]->ope[3],ope[2]->ope[1]-ope[2]}";



Clear[getInverseTransformation]
getInverseTransformation[listRules_]:=Module[{rules,subsetsRules,inverseRules,submatrix,opesInSubset},
(*Re-label ope by opeA (LHS) and opeB (RHS)*)
rules=listRules/.(lhs_->rhs_):>Inactive[Rule][lhs/.ope[n_]:>opeA[n],rhs/.ope[m_]:>opeB[m]];

(*Group the rules based on the opes in the RHS. Works for 2x2 subtransformations (or dense/full nxn)*)
subsetsRules=GatherBy[rules,Cases[#,opeB[_],Infinity]&]/.{opeA[n_]->ope[n],opeB[n_]->ope[n]};

(*Initialize list to store the inverse rules*)
inverseRules=ConstantArray[0,Length[subsetsRules]];

(*For each subtransformation, get the 2x2 submatrix (or nxn), invert it, and create the inverted Rule*)
(*Trying to use Inverse on the whole matrix for large Lagrangians crashes MMA*)
Do[
opesInSubset=subsetsRules[[i]][[All,1]];
submatrix=CoefficientArrays[subsetsRules[[i]][[All,2]],opesInSubset][[2]];
inverseRules[[i]]=MapThread[Rule,{opesInSubset,Inverse[submatrix] . opesInSubset}];
,{i,Length[subsetsRules]}
];

inverseRules=inverseRules/.Power[ii,-1]->-ii//Flatten//Sort
]

getInverseTransformation::usage = 
"getInverseTransformation[listRules_] takes the set of rules listRules and returns the inverse transformation. 
Rules with inear combinations must contain the same ope numbers in LHS and RHS. For example: 
listRules={ope[i] -> ope[i] + ope[j] , ope[j] -> ope[i] - ope[j]}
This is fonr automaticslly by getTransformationRules.";

Clear[getInverseTransformationNaive]
getInverseTransformationNaive[listRules_]:=listRules/. (ope[i_] -> a_. ope[j_]):>(ope[j] -> (1/a) ope[i]);


(* ::Subsection::Closed:: *)
(*reverseTR: Matrix transpose*)


Clear[reverseTR]
reverseTR[terms_]:=terms/.TR[a__]:>TR[Sequence@@Reverse[{a}]];

reverseTR::usage = 
"reverseTR[terms_] reverses the order of the arguments in every TR appearing in terms.";


(* ::Subsection::Closed:: *)
(*Reorder terms*)


Clear[reorderOperators]
reorderOperators[scoreFunction_][terms_]:=SortBy[terms,scoreFunction]//Reverse

Clear[moveUp]
moveUp[elements_][list_] := Module[{remaining, movedUp},
  movedUp = Select[list, MemberQ[elements, #] &];
  remaining = Complement[list, movedUp];
  Join[movedUp, remaining]
]

moveUp::usage = 
"moveUp[elements_][list_] returns a reordered list with elements at the beginning";

reorderOperators::usage = 
"reorderOperators[scoreFunction_][terms_] calculates the score of each term, according to the 
user-defined scoreFunction, and reorders the terms accordingly";


Clear[getTransformationRulesFromListOrder]
getTransformationRulesFromListOrder[opesOrdered_]:= opesOrdered//MapIndexed[#1->ope[Sequence @@#2]&](*ope[old]->ope[new]*)

getTransformationRulesFromListOrder::usage =
"getTransformationRulesFromListOrder[opesOrdered_] returns a set of rules like {ope[i] -> ope[j]} where j is the position 
in opesOrdered that ope[i] occupies";


scorePreferredOperators::usage = 
"scorePreferredOperators[terms_] is a user-defined function that takes a term and returns a score. 
A higher score means the term will be preferentially kept in the final basis. To aid the construction of 
scorePreferredOperators, these functions are available:
 - nFields[term_,field_] : number of instances of field in term
 - nDer[term_] : total number of derivatives
 - nSeqDer[term_] : max number of sequential derivatives, on the same field
 - nTraces[term_] : number of traces
 - hasField[term_,field_] : output is 1 if term contains field; 0 otherwise
 - hasNotHas[term_,has_,nothas_] : like hasField but term should cannot contain the fields in 'nothas'
The argument fied may contain Alternative (field1|field2|field3)

If you dont care for now about which terms are kept, let mathematica choose:

Clear[scorePreferredOperators]
scorePreferredOperators[terms_] := Identity[terms]

(this should be the deffault ONE DAY)";


Clear[scorePreferredOperators]
scorePreferredOperators[terms_] := Identity[terms] 
(*Is that day TODAY?*)


Clear[nFields,nDer,nSeqDer,nTraces,hasField,hasNotHas]
nFields[term_,field_]:=Count[term,field,Infinity,Heads->True]
nDer[term_]:=Total[Cases[term,DD[f_,nder_][___]:>nder,Infinity]]
nSeqDer[term_]:=Max[Cases[term,DD[f_,nder_][___]:>nder,Infinity]]
nTraces[term_]:=Count[term,TR,Infinity,Heads->True]
hasField[term_,field_]:=If[nFields[term,field]>=1, 1, 0]
hasNotHas[term_,has_,nothas_]:=If[nFields[term,has]>=1&&nFields[term,nothas]==0, 1, 0]

nFields::usage = "nFields[term_,field_] see scorePreferredOperators";
nDer::usage = "nDer[term_] see scorePreferredOperators";
nSeqDer::usage = "nSeqDer[term_] see scorePreferredOperators";
nTraces::usage = "nTraces[term_] see scorePreferredOperators";
hasField::usage = "hasField[term_,field_] see scorePreferredOperators";
hasNotHas::usage = "hasNotHas[term_,has_,nothas_] see scorePreferredOperators";


Clear[remove]
remove[elementsToRemove_][list_] :=Module[{rm},
rm=elementsToRemove//Map[#->0&]//rulesToFunction;
list//rm
]


remove::usage = 
"remove[elementsToRemove_][list_] sets to zero the elementsToRemove that are found in list";


(* ::Section::Closed:: *)
(*[Functions] Gaussian Elimination*)


(* ::Text:: *)
(*Different methods explained in*)
(*https://mathematica.stackexchange.com/questions/283946/rank-of-singular-large-sparse-matrices*)


(* ::Subsection::Closed:: *)
(*Construct matrix*)


Clear[getRelationMatrix]
getRelationMatrix[list__]:=Module[{aux = list,aux2,notNumericSymbols},

(*create matrix*)
Print["\nCreating matrix from ",Length[aux//Flatten]," relations..."];

Print["Separating real and imaginary parts..."];
(*Prepare *)
aux= (aux  /.ii->I//Expand) /.Complex[re_,im_]:>re + im ii/.ii^2->-1//Flatten;
aux=Join[aux//Map[Coefficient[#,ii]&],aux//Map[Coefficient[#,ii,0]&]]//DeleteCases[0];
aux = aux //SortBy[Count[#,ope[_],99]&];

(*Sanity check*)
notNumericSymbols=Cases[aux/.ope[_]->1,_ * _?(!NumericQ[#]&),99]//DeleteDuplicates;
If[notNumericSymbols =!={},Print["\nERROR: Non numeric symbols found in the relations: ", Take[notNumericSymbols,Min[5,Length[notNumericSymbols]]]];Abort[]];

Print["Extracting coefficients and building SparseArray..."];
aux2=aux;(*having another aux2 speeds up a factor 50*)
Do[aux2[[j]]=aux[[j]]/.ope[n_]:>ope[n,j],{j,Length[aux]}];

aux2 = (aux2//Map[plusToList]);
aux2 = aux2/.a_. ope[n__]:>({n}->a)//Flatten;
SparseArray[aux2]//Transpose
]

(*{relBIp,relEOM}/.Nf\[Rule]8//Flatten//#[[15;;-1;;5]]&;
aux=Flatten[%] // rawToSymOpesF //symToPrefOpesF;
{aux}//getRelationMatrix;
%//MatrixPlot*)

getRelationMatrix::usage = 
"getRelationMatrix[list__] returns a SparseArray encoding all the monomial relations. These must be supplied as a list of
ope number combinations, e.g. list = {{ope[5] - 2 ope[8]}, {ope{3} + I ope[4}}. The input operators MUST be symmetric under H.";


(* ::Subsubsection::Closed:: *)
(*Inspect relation matrix*)


Clear[inspectRelationMatrix]
inspectRelationMatrix[relationMatrix_]:=Module[
{aux = relationMatrix,plot,accumulatedValues,textPosition,mantissa, exponent,top,step,opts,lines,textLabels},

Print["This relation matrix contains ", Dimensions[relationMatrix]//First , " relations between ", Dimensions[relationMatrix]//Last, " operators"];

aux = aux//ArrayRules;
aux = aux /.({a_,b_}->c_):>a//Tally;
aux = aux /.{a_,b_}:>b//Tally;

Print["{Number of opes in relation, number of relations}"];
Print[aux];


top = First[Dimensions[relationMatrix]];
accumulatedValues = top-Accumulate[aux[[All, 2]]];
textPosition = 0.5 (*no effect*);

{mantissa, exponent} = MantissaExponent[top]//N;
step= 10^(exponent-1) *Nearest[{0.1, 0.2, 0.5},mantissa][[1]];

opts=Sequence[AspectRatio -> 1, PlotRangePadding -> 0, ImagePadding -> 38];
plot=MatrixPlot[relationMatrix,opts,FrameTicks->{Range[0,Ceiling[top,step],step],Automatic},MaxPlotPoints->300];


lines = Graphics[{Red, Table[Line[{{1, i}, {Last[Dimensions[relationMatrix]], i}}], {i, accumulatedValues}]},opts];
textLabels = Graphics[{Red, Table[
   Text[ToString[aux[[i, 1]]] <> " terms \n ", {textPosition, accumulatedValues[[i]] + 1500}],
   {i, Length[aux]}]},opts];


Overlay[{plot,Graphics[lines],Graphics[textLabels]}]
]

(*relationMatrix//inspectRelationMatrix*)


(* ::Subsection::Closed:: *)
(*Get Basis*)


Clear[getMinimalBasis]
getMinimalBasis[A_SparseArray]:=Module[{matrixPath,cmdCompile,cmdRun,env,stdout,diag,basis, D,P},

Print["Factorising ..."];

(*Save matrix; compile; run SPQR with matrix as argument*)
Quiet@CreateDirectory[NotebookDirectory[]<>"tmp"];
matrixPath=Export[NotebookDirectory[]<>"tmp/mat.mtx",A];
cmdCompile="g++ "<>directoryOfMINIBAR<>"SPQR/decQR.cpp "<>"-lcholmod -lspqr -lsuitesparseconfig -o "<>NotebookDirectory[]<>"tmp/tmp"; 
cmdRun=NotebookDirectory[]<>"tmp/tmp "<>matrixPath; 
Print[cmdRun];

env=<|"LD_LIBRARY_PATH"->pathToSuiteSparse<>"/CHOLMOD/build:"<>pathToSuiteSparse<>"/SPQR/build:$LD_LIBRARY_PATH"|>;
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,All,cmdRun,ProcessEnvironment->env];
If[stdout["ExitCode"]==0,stdout["StandardOutput"]//Print,"\n\n\nERROR: "<>stdout["StandardError"]<>"\n\n\n"//Print];


D=Import[NotebookDirectory[]<>"tmp/matOutD.mtx"];
P=ReadList[NotebookDirectory[]<>"tmp/permOut.txt",Number] + 1; (*correct 0-based vector*)

{D,P}=Chop[{D,P}];

diag=Table[D[[i,i]],{i,Min[Dimensions[D]]}];
basis=Position[diag[[Ordering[P]]],0]//Map[#/.{n_}:>ope[n]&];

Print["Minimal basis obtained:  ", Length[basis], " operators altogether"];

basis


]

getMinimalBasis::usage =
"getMinimalBasis[A_SparseArray] performs the reduction to a minimal basis of operators based on the relations 
found between monomials, which are given as input through the SparseArray A, generated by getRelationMatrix.

Needs installation of SuiteSparseQR and its dependencies (see GitHub>MINIBAR>SPQR).";



Clear[getMinimalBasisAndRelations]
getMinimalBasisAndRelations[A_SparseArray]:=Module[{matrixPath,cmdCompile,cmdRun,env,stdout,diag,basis, D,P,R},


Print["Factorising ..."];

If[Max@@Dimensions[A]>1000, 
Print[
"It seems like you have a large relation matrix. If you ONLY want the basis use instead getMinimalBasis
and cancel the C++ process in a terminal with 'killall -9 tmp'. No, Alt+. in Mathematica will not stop it.

To obtain the relations, the full upper triangular matrix R of the QR decomposition is written into matOutR.mtx.
This can take long and the file weight several Gb, since it is a dense matrix. \n"]];

(*Save matrix; compile; run SPQR with matrix as argument*)
Quiet@CreateDirectory[NotebookDirectory[]<>"tmp"];
matrixPath=Export[NotebookDirectory[]<>"tmp/mat.mtx",A];
cmdCompile="g++ "<>directoryOfMINIBAR<>"SPQR/decQR_returnFullR.cpp "<>"-lcholmod -lspqr -lsuitesparseconfig -o "<>NotebookDirectory[]<>"tmp/tmp"; 
cmdRun=NotebookDirectory[]<>"tmp/tmp "<>matrixPath; 
Print[cmdRun];

env=<|"LD_LIBRARY_PATH"->pathToSuiteSparse<>"/CHOLMOD/build:"<>pathToSuiteSparse<>"/SPQR/build:$LD_LIBRARY_PATH"|>;
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,All,cmdRun,ProcessEnvironment->env];
If[stdout["ExitCode"]==0,stdout["StandardOutput"]//Print,"\n\nERROR: "<>stdout["StandardError"]//Print;Abort[]]; (*LINE NOT TESTED HERE*)

D=Import[NotebookDirectory[]<>"tmp/matOutD.mtx"];
R=Import[NotebookDirectory[]<>"tmp/matOutR.mtx"];
P=ReadList[NotebookDirectory[]<>"tmp/permOut.txt",Number] + 1; (*correct 0-based vector*)

{D,R,P}=Chop[{D,R,P}];

diag=Table[D[[i,i]],{i,Min[Dimensions[D]]}];
basis=Position[diag[[Ordering[P]]],0]//Map[#/.{n_}:>ope[n]&];

Print["Minimal basis obtained:  ", Length[basis], " operators altogether"];

{basis,R}

]

getMinimalBasisAndRelations::usage =
"getMinimalBasisAndRelations[A_SparseArray] is like getMinimalBasis but in addition it saves and returns the relation
matrix R after the Gaussian Elimination. To catch the output: 
{basis,R} = getMinimalBasisAndRelations[relMatrix]

There are no functions to process R but basically one has to:
 - Decide which operator numbers are interesting, opelist. 
 - R[[All,opelist]] returns those columns of R.
 - Convert these columns (SparseArray) to a readable format with ArrayRules. Format is {irel, open}->factorInRelation
 - Now extract the row numbers of the nonempty spots of the column: Get the list in irelList
 - Get the rows = R[[irelList]]
 - rows //ArrayRules
 - Gather elements with irel: GatherBy[%,#[[1,1]]&]
 - ({irel, open}->factor):> factor*ope[open]
 - %//Map[Total] gives a list of relations

 - The interesting thing might be to find relations that share two of the operators ope[n] and ope[m]. For that the 
simplest is to obtain the list of relations for all potentially interesting operators (like above). Then Select those that 
contain one specific ope[n], repeat for ope[m]. Find the Intersection of the result.

I had a code for all this that I lost, but in fact looking at these huge relations was useless in my case anyway.

Needs installation of SuiteSparseQR and its dependencies (see GitHub>MINIBAR>SPQR).";



(* ::Subsection::Closed:: *)
(*Get Rank*)


(* ::Text:: *)
(*  - getRank: Uses SparseQR. Performs QR decomposition, where R is upper triangular. Rank is the number of nonzero elements in the diagonal. Needs installation of SuiteSparse and its dependencies. Get it running first in C++. This is faster than getMinimalBasis because we don't impose preferred operators and allow highly-optimized row and column swaps*)
(*  - getRankMathematicaQuick = SparseMatrixRank (stackexchange) = LinearSolve::Multifrontal = UMFPACK: Built-in Mathematica. Uses fast LU decomposition. But generally fails with large singular matrices*)
(* - getRankMathematica = RRMCF. Basic LU decomposition. Slow. Not optimized for sparse matrices. Gives the correct answer. Explicit algorithm explained in https://www.sciencedirect.com/science/article/pii/S0024379506002011 *)
(**)
(* Getting the rank of a large matrix in Mathematica isn't straightforward. I explained the situation in https://mathematica.stackexchange.com/questions/283946/rank-of-singular-large-sparse-matrices*)


(* ::Subsubsubsection::Closed:: *)
(*SuiteSparseQR*)


Clear[getRank]
getRank[A_SparseArray]:=Module[{matrixPath,cmdCompile,cmdRun,env,stdout,rank,nvariables},
(*Save matrix; compile; run SPQR with matrix as argument*)
Quiet@CreateDirectory[NotebookDirectory[]<>"tmp"];
matrixPath=Export[NotebookDirectory[]<>"tmp/mat.mtx",A];
cmdCompile="g++ "<>directoryOfMINIBAR<>"SPQR/rankQR.cpp "<>"-lcholmod -lspqr -lsuitesparseconfig -o "<>NotebookDirectory[]<>"tmp/tmp"; 
cmdRun=NotebookDirectory[]<>"tmp/tmp "<>matrixPath; 


env=<|"LD_LIBRARY_PATH"->pathToSuiteSparse<>"/CHOLMOD/build:"<>pathToSuiteSparse<>"/SPQR/build:$LD_LIBRARY_PATH"|>;
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,All,cmdRun,ProcessEnvironment->env];
If[stdout["ExitCode"]==0,stdout["StandardOutput"]//Print,"\n\nERROR: "<>stdout["StandardError"]//Print;Abort[]]; (*LINE NOT TESTED HERE*)

(*env=<|"LD_LIBRARY_PATH"->"/home/etlar/joan/Programs/SuiteSparse-7.0.1/CHOLMOD/build:$LD_LIBRARY_PATH"|>;
(*env=<|"LD_LIBRARY_PATH"->"/home/joanruiz/Programs/SuiteSparse-7.0.1/lib:$LD_LIBRARY_PATH"|>;*)
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,"StandardOutput",cmdRun,ProcessEnvironment->env];
stdout//Print;
*)

rank=stdout["StandardOutput"]//StringTake[#,-10]&//ToExpression;

nvariables = Last[Dimensions[A]];
Print["Nbr. of monomials: ", nvariables ];
Print["Nbr. of independent relations (rank): ",rank];
Print["Nbr. of independent monomials: ", nvariables-rank];

rank
]

getRank::usage = 
"getRank[A_SparseArray] returns the rank of the matrix A. This is the number of independent relations, 
each of which removes one operator from the basis. 

Needs installation of SuiteSparseQR and its dependencies (see GitHub>MINIBAR>SPQR).";


(* ::Subsubsubsection::Closed:: *)
(*Mathematica versions*)


Clear[getRankMathematica]
getRankMathematica[A_SparseArray]:=Module[{L,U,m,n,rk,ck,rank=0,auxA=A,js,subt,nvariables},

{m,n}=Dimensions[A];
L=IdentityMatrix[m,SparseArray];
subt=ConstantArray[0,m];

(*Loop over all rows i that aren't zero *)
PrintTemporary["Looping over (max) ",m," relations... "];Monitor[
Do[
If[Total[Abs[auxA[[i]]]]!=0,
rank++; 

(*Pivot indices {rk,ck}*)
rk=i;
ck=auxA[[i]]["NonzeroPositions"][[FirstPosition[Flatten[auxA[[i]]["NonzeroValues"]],_?(#!=0&)][[1]]]][[1]];

(*Preselect which rows (js) have nonzero elements below the pivot*)
js=Select[Flatten[auxA[[All,ck]]["NonzeroPositions"]],(#>=rk+1&)];
js=Select[js,(auxA[[#,ck]]!=0&)];

(*Make zero all elements below the pivot auxA[[rk,ck]] *)
L[[js,rk]]=auxA[[js,ck]]/auxA[[rk,ck]];
Do[subt[[j]]=L[[j,rk]]*auxA[[rk]],{j,js}];
auxA[[js]]-=subt[[js]];

,{}];

,{i,m}];
,i];

U=auxA;
If[A!=L . U, Print["getRankMathematica FAILED with this matrix. Use getRankMathematicaQuick or getRank (needs SuiteSparseQR)"];Return[Null]];

nvariables = Last[Dimensions[A]];
Print["Nbr. of monomials: ", nvariables ];
Print["Nbr. of independent relations (rank): ",rank];
Print["Nbr. of independent monomials: ", nvariables-rank];

rank
]


Clear[getRankMathematicaQuick]
getRankMathematicaQuick[A_SparseArray?MatrixQ]:=Module[{a,S,U,L,p,q,d1,d2,rank,nvariables},{d1,d2}=Dimensions[A];

a=If[d1>d2,Join[Transpose[A],SparseArray[{},{d1-d2,d1},A["Background"]]],Join[A,SparseArray[{},{d2-d1,d2},A["Background"]]]];
S=Quiet@LinearSolve[a,Method->"Multifrontal"];
U=S["getU"];
L=S["getL"];
{p,q}=S["getPermutations"];


If[(L . U)[[p,q]]!=a, Print["getRankMathematicQuick FAILED with this matrix. Use getRankMathematica or getRank (needs SuiteSparseQR)"];Return[Null]];

rank = Total[Unitize[Diagonal[Chop[U]]]];

nvariables = Last[Dimensions[A]];
Print["Nbr. of monomials: ", nvariables ];
Print["Nbr. of independent relations (rank): ",rank];
Print["Nbr. of independent monomials: ", nvariables-rank];

rank
];




Clear[toSquare]
toSquare[A_SparseArray]:=Module[{m,n,auxA=A},
{m,n}=Dimensions[A];
Print["Making a square from (",m ,", ",n,") dimensions..."];
auxA=If[m>n,Join[Transpose[A],SparseArray[{},{m-n,m},A["Background"]]],Join[A,SparseArray[{},{n-m,n},A["Background"]]]]
]

getRankMathematica::usage = 
"getRankMathematica[A_SparseArray] returns the rank of the matrix A. This is the number of independent relations, 
each of which removes one operator from the basis. It uses a rank-revealing algorithm of LU decomposition.

For near-square relation matrices this (undocumented Mathematica function) works (slightly) faster,
p = relationMatrix//toSquare//SparseArray`ApproximateMinimumDegree[#]&; (*Re-order rows before doing the decomposition*)
relationMatrix[[All,p]]//getRankMathematica
";

getRankMathematicaQuick::usage = 
"getRankMathematicaQuick[A_SparseArray] returns the rank of the matrix A. 
Uses the UMFPACK algorithm through the Mathematica built-in functon LinearSolve::Multifrontal.
May fail for large singular matrices";




(* ::Subsection::Closed:: *)
(*Summary of basis*)


Clear[summary]
summary[basis_,{applySym__},vanishRules___]:=Module[{basisEven,basisSubset,nSymEven},

Print["\nSummary of the final minimal basis:"];


basisEven = basis *Times@@((signsUnder[#][basis]/.-1:>0)&/@{applySym})//DeleteCases[0];
nSymEven = basisEven//Length;
If[nSymEven ==0, 
Print["Could not determine if the terms are even or odd.\n" ];basisEven=basis,
Print["\n    -",  nSymEven , " even terms \n    -", Length[basis]-nSymEven, " odd terms \n"]
];

Print["All terms     "," - ", Length[basisEven], " terms"];

If[Length[{vanishRules}]!=0,

i=1;
Table[
basisSubset[i] = basisEven/.rule/.TR[___ , DD[0,_][___] , ___]:>0//DeleteCases[0]//DeleteDuplicates;
Print["Basis subset ",i," - ", Length[basisSubset[i]], " terms"];
i++;
,{rule,{vanishRules}}];

maxLength = Max[Length/@basisSubset/@Range@Length[{vanishRules}]];
If[maxLength<= 50, 
Print["\n BASES (specified subsets): "];
Join[{Range[maxLength]},basisSubset/@Range[Length[{vanishRules}]]]//Transpose@PadRight[#, Automatic, ""]&//TableForm//see;
];

];

basisEven
];

summary::usage = 
"summary[basis_,{applySym__},vanishRules___] prints a summary of the final basis. It will show how 
many monomials are even under all the symmetries specified in applySym (these functions transform 
the terms, and reshape them afterwards); returning the even monomials. It will also show the number 
of terms surviving when some fields are zero, which can be specified in vanishRules simply like 
(field1|field2):>0.
If the resulting subsets of the basis have less than 50 terms it will print them. ";


Clear[removeTermsWith]
removeTermsWith[f__][list_]:=list/.TR[___,DD[Alternatives[f],_][___],___]:>0//DeleteCases[0];

removeTermsWith::usage=
"removeTermsWith[f__][list_] removes terms in list that contain the field f";

Clear[removeTermsWithout]
removeTermsWithout[f__][list_]:=Complement[list,removeTermsWith[f][list]]

removeTermsWithout::usage=
"removeTermsWithout[f__][list_] removes terms in list that do NOT contain the field f";


(* ::Subsection::Closed:: *)
(*Test equivalence of bases*)


Clear[testEquivalenceBases]
testEquivalenceBases[base1_,base2_,rel_]:=Module[{b1,b2, b1AuxOpe,b1AuxToOrigOpe,b1Relations,MB1,b1InMB1,b2AuxOpe,b2AuxToOrigOpe,b2Relations,MB2,b2InMB2},

b1=base1;
b2=base2;

(*Prepare input into b1, b2*)
b1=b1//removeTags[opeH|opeJ|ope1|ope2|ope3];
b2=b2//removeTags[opeH|opeJ|ope1|ope2|ope3];

If[Length[b1]=!=Length[b2], Print["WARNING: The two bases have different lengts. Testing if they fill the same operator space..."]];
If[!DuplicateFreeQ[b1]||!DuplicateFreeQ[b2], Print["WARNING: There are duplicate elements in the bases. Removing them."]];

b1=b1//DeleteDuplicates;
b2=b2//DeleteDuplicates;

(*BASIS 1 *)
b1AuxOpe = rel//additionalOpesFor[b1];
b1Relations= b1AuxOpe - b1;

MB1 = rel // Append[b1Relations] // getRelationMatrix //getMinimalBasis;
b1InMB1 = Intersection[b1AuxOpe,MB1];

If[Length[MB1]==0, Print["ERROR: Gaussian elimination failed. Try comparing subsets of the bases"];Abort[]];

(*BASIS 2 *)
b2AuxOpe = rel //additionalOpesFor[b2];
b2Relations= b2AuxOpe - b2;

MB2 = rel // Append[b2Relations] // getRelationMatrix //getMinimalBasis;
b2InMB2 = Intersection[b2AuxOpe,MB2];

If[Length[MB2]==0, Print["ERROR: Gaussian elimination failed. Try comparing subsets of the bases"];Abort[]];

Print["\nBASIS 1: "];
b1AuxOpe//isCompleteAndMinimalWrt[MB1];
Print["BASIS 2: "];
b2AuxOpe//isCompleteAndMinimalWrt[MB2];

If[Complement[MB1,b1AuxOpe]//ContainsExactly[Complement[MB2,b2AuxOpe]], (*Cover same space?*)
If[Length[b1AuxOpe]>Length[b1InMB1] || Length[b2AuxOpe]>Length[b2InMB2] , (*Equivalent?*)
Print["\nBases 1 & 2: cover the SAME operator space"] , 
Print["\nBases 1 & 2: are EQUIVALENT"] ],
Print["Bases 1 & 2: cover DIFFERENT operator spaces"]
];

]

Clear[isCompleteAndMinimalWrt]
isCompleteAndMinimalWrt[MB1_][b1_]:=Module[{b1InMB1},

b1InMB1 = Intersection[b1,MB1];

Which[
Length[b1]==Length[MB1], Print["COMPLETE and MINIMAL"],
Length[b1]>Length[MB1] && Length[b1InMB1]==Length[MB1], Print["OVERCOMPLETE: ", Length[b1]-Length[b1InMB1], " redundant operators"],
Length[b1]<Length[MB1] && Length[b1]==Length[b1InMB1], Print["NOT COMPLETE but MINIMAL"],
Length[b1]<Length[MB1] && Length[b1]>Length[b1InMB1], Print["NOT COMPLETE and NOT MINIMAL: ", Length[b1]-Length[b1InMB1], " redundant operators"]];
]

isCompleteAndMinimalWrt::usage=
"isCompleteAndMinimalWrt[MB1_][b1_] tests if the basis b1 is complete and minimal. It assumes that the 
minimal basis MB1 contains all terms in b1 that are linearly independent among them. It is used 
INTERNALLY by getRedundantOperatorsUsing and testEquivalenceBases";

testEquivalenceBases::usage=
"testEquivalenceBases[base1_,base2_,rel_] tests if base1 and base2 are equivalent when given the set
of operator relations rel.

Does not work with complete bases. Test a subset: for example removeTermsWith[field1|field2]. 
Or if the two bases share one operator, it is enough removing it from both bases";


Clear[getRedundantOperatorsUsing]
getRedundantOperatorsUsing[rel_][base1_]:=Module[{unwantedTags,foundTags,b1InMB1,b1,b1AuxOpe,b1Relations,MB1,b1AuxToOrigOpe},

b1=base1;
b1=b1//removeTags[opeH|opeJ|ope1|ope2|ope3];

If[!DuplicateFreeQ[b1], Print["WARNING: There are duplicate elements in the basis. Removing them."]];
b1=b1//DeleteDuplicates;

(*Get Minimal basis MB appending b1 to the relations*)
b1AuxOpe = rel//additionalOpesFor[b1];
b1Relations= b1AuxOpe - b1;
b1AuxToOrigOpe = #/.MapThread[Rule,{b1AuxOpe,b1}] &;

MB1 = rel // Append[b1Relations] // getRelationMatrix //getMinimalBasis;
b1InMB1 = Intersection[b1AuxOpe,MB1];

(*Return redundant*)
Print["The provided basis is: "];
b1AuxOpe//isCompleteAndMinimalWrt[MB1];
Complement[b1AuxOpe,b1InMB1]//b1AuxToOrigOpe

]


Clear[toOpeTagsIn]
toOpeTagsIn[baseTwoTags_][prefopes_]:=Module[{},
prefopes//Map[(baseTwoTags/.#:>1/.ope[_]:>0//DeleteCases[0])&]//Flatten]

Clear[removeTags]
removeTags[unwantedTags_][terms_]:= Module[{foundTags},
foundTags=FirstCase[terms,unwantedTags,Null,99,Heads->True];
If[foundTags=!=Null,Print["INFO: Removed spurious ", foundTags, " tags"]];
terms/.List@@(#[_]:>1&/@unwantedTags)]

getRedundantOperatorsUsing::usage = 
"getRedundantOperatorsUsing[rel_][base1_] tests if the base1 is minimal when given the set of relations rel between monomials. 
Returns the list of redundant operators (that are linearly dependent on the rest).

The operators must be written as ope[12], and the translation into terms managed outside the program";

toOpeTagsIn::usage = 
"toOpeTagsIn[baseTwoTags_][prefopes_] translates the ope[i] tags in prefopes to the companion tag (e.g. opeH[j]) 
present in the elements of baseTwoTags";

removeTags::usage = 
"removeTags[unwantedTags_][terms_] removes from terms the unwantedTags, that are given as opeH|ope1|ope2 and appear in terms
with one argument like opeH[13]";


(* ::Text:: *)
(*Simply check which terms are different at face value*)


Clear[basesDiff]
basesDiff[basis1_,basis2_]:=Module[{},
Print["Terms only in basis 1"];
Complement[basis1,basis2]//see;
Print["Terms only in basis 2"];
Complement[basis2,basis1]//see;]

basesDiff::usage=
"basesDiff[basis1_,basis2_] shows which terms exist only in basis1 and which only in basis2";


(* ::Subsection::Closed:: *)
(*Extend basis*)


Clear[additionalOpesFor]
additionalOpesFor[terms_List][relationMatrix_SparseArray] := 
ope/@Range[Last[Dimensions[relationMatrix]]+1 , Last[Dimensions[relationMatrix]] + Length[terms]]

additionalOpesFor[terms_List][rel_List] := Module[{maxOpe},
maxOpe=(Cases[rel,ope[n_]->n,99]//Max);
ope/@Range[maxOpe+1 , maxOpe + Length[terms]]]

additionalOpesFor::usage = 
"additionalOpesFor[terms_List][relationMatrix_SparseArray] returns a list of ope[i], to identify the terms. 
Starts counting after the largest ope[i] of the second argument, which can be a relationMatrix (SparseArray)
or a List of ope relations. ";


(* ::Section::Closed:: *)
(*End package*)


EndPackage[]
