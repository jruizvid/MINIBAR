(* ::Package:: *)

(* ::Section::Closed:: *)
(*miniBASIS*)


(* ::Text:: *)
(*Tools to calculate minimal Lagrangians explicitly with Mathematica*)
(*version 0: XX September 2023*)
(**)
(*Author: Joan Ruiz-Vidal*)


(* ::Section::Closed:: *)
(*Declaration*)


(* ::Text:: *)
(*This software provides a set of tools to aid the calculation of operator bases in QFT Lagrangians.*)
(*These tools have been developed for the case of Chiral Perturbation Theory (ChPT) with pseudoscalar mesons and external fields, and, in particular, to obtain the anomalous Lagrangian of ChPT at order p6/p8. The two given examples of minimal bases lead to the final result, written in two different parameterizations of the field content.*)
(**)
(*The underlying algorithms and structure of the calculation has been shaped in collaboration with *)
(* - Johan Bijnens (Lund University)*)
(* - Nils Hermansson-Truedsson (Lund University; Edinburgh University) *)
(**)
(*Both of them posses extensive expertise in these analyses and conducted independent calculations of this Lagrangian with a different software.*)
(**)
(*Crucial inputs for constructing and optimizing part of the code presented here were generously provided by the community of mathematica.stackexchange.com.*)


(* ::Section:: *)
(*Structure of this file*)


(* ::Text:: *)
(*Usage:*)
(* - Execute the "Core functions" altogether*)
(* - In the examples, execute the "Configuration" first. Some functions there replace the dummy definitions in the Core functions, so do not execute these again*)
(* - The calculation itself is written synthetically using the functions defined in "Core functions" (genuine miniBASIS), and "Configuration" (user defined)*)
(*  *)
(*Overview:*)
(* - "Compose terms" constructs the possibleTerms. Fields and derivatives are combined, traces applied and indices distributed in all the possible combinations.*)
(* - "Trivial relations" reduces the list of possibleTerms accounting for obvious zeroes, permutations of indices and cyclicity of traces.*)
(* - "Operator relations" builds the relations between terms, based on some identities given by the user. Helper functions to include Cayley-Hamilton trace relations, Total derivatives, and the Schouten identity are native in miniBASIS.*)
(* - "Transform and reorder terms" redefines the basis to make every operator Hermitian, and optionally also even under a set of user-defined discrete symmetries (P,C). It also determines which operators should be preferentially kept in the final basis*)
(* - "Gaussian elimination" finds the minimal basis from the set of operator relations*)
(* *)
(*Notation of the fields:*)
(*  - DD[field, n][a,b,...] for a field with n covariant derivatives The indices {a,b,...} belong to the derivatives and the field itself, in order.*)
(**)


(* ::Chapter::Closed:: *)
(*Core functions*)


(*BeginPackage["miniBASIS`"]*)


$HistoryLength=3; (*Don't waste RAM*)


(* ::Section::Closed:: *)
(*[Functions] General helpers*)


(* ::Subsubsection::Closed:: *)
(*Save *)


Clear[save]
save[where_][what__]:=Module[{directory,symbols},
directory=NotebookDirectory[]<>"/save/"<>where<>".mx";
If[! DirectoryQ[DirectoryName[directory]],
    CreateDirectory[DirectoryName[directory]]];
    symbols=ToString/@{what};
DumpSave[directory,symbols];]

Clear[import]
import[where_]:=Get[NotebookDirectory[]<>"/save/"<>where<>".mx"]


(* ::Subsubsection::Closed:: *)
(*Change headers, deactivate Power and Times*)


(* ::Input:: *)
(*Clear[plusToList]*)
(*plusToList=If[Head[#]===Plus&&Head[#]=!=List,List@@#,If[Head[#]=!=List,List@#,#]] &;*)
(**)
(*plusToList::usage = *)
(*"plusToList returns the list of summands in a expression with head Plus. *)
(*Inverse of Total: y //plusToList //Total = y";*)


(* ::Input:: *)
(*(*Define the symbol "Subscript[/@, n] to Map any expression at level n" *)*)
(*MakeExpression[RowBox[{f_,SubscriptBox["/@",n_],expr_}],StandardForm]:=MakeExpression@RowBox[{"Map","[",f,",",expr,",","{",n,"}","]"}]*)
(*(*list={{a,b},{d,{g,y},h,y},{q,r,w}};*)
(*\!\(F*)
(*\*SubscriptBox[\(/@\), \(2\)]list\)*)*)
(**)


(* ::Input:: *)
(*Clear[inactivePower]*)
(*inactivePower[expr_]:=expr/.Power[a_,b_?IntegerQ]:>(Inactive[Times]@@ConstantArray[a,b])*)
(**)
(*inactivePower::usage := "inactivePower[expr_] turns every Power in expr into an explicit product and freezes its order"*)


(* ::Subsubsection::Closed:: *)
(*showTiming. showLength*)


(* ::Input:: *)
(*Clear[showTiming]*)
(*showTiming[in_]:=Block[{res},res=AbsoluteTiming[in];Print[res[[1]]," s"];res[[2]]]*)
(*SetAttributes[showTiming,HoldAll] (* <-IMPORTANT!*)*)
(**)


(* ::Input:: *)
(*showLength[in_]:=Block[{res},res=in;Print[Length[res]," terms"];res]*)
(*SetAttributes[showLength,HoldAll] *)


(* ::Input:: *)
(*showLengthNo0[in_]:=Block[{res},res=in;Print[Count[res,_?(#=!=0&)]," terms"];res]*)
(*SetAttributes[showLengthNo0,HoldAll] *)
(**)


(* ::Input:: *)
(*showLengthFlat[in_]:=Block[{res},res=in;Print[Length[Flatten[res]]," terms"];res]*)
(*SetAttributes[showLength,HoldAll] *)


(* ::Subsection:: *)
(*Helpers to debug / read terms*)


(* ::Subsubsection:: *)
(*Pleasant notation*)


(* ::Text:: *)
(*To inspect the terms we define the function "see". To use it, the user must define two functions*)
(*  - "nIndices[field]" gives the number of indices of each field -  is defined with the information inside BB (building blocks)*)
(*  - "cal[field]" gives the calligraphic symbol of each field*)


Clear[readableNotation]
readableNotation[expr_]:=expr/.DD[field_,nder_][ind___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
nInd=Length[{ind}]-nder;
Which[
nInd==0 &&nder==0,cal[field] ,
nInd==0 &&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}].(cal[field]),
nInd!= 0&&nder==0, Subscript[cal[field], Sequence@@List[indMod]],
nInd!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}].(Subscript[cal[field], Sequence@@List[indMod][[nder+1;;nder+nInd]]])])

Clear[readableIndex]
readableIndex[index_] := index /. {i_Symbol[n_Integer] :> ToString[i] <> ToString[n]}



Clear[readableNotationOLD]
readableNotationOLD[expr_]:=expr/.DD[field_,nder_][ind___]:>(
indMod = {ind}//readableIndex//Sequence@@#&;
Which[
(nIndices[field]==0||!NumericQ[nIndices[field]])&&nder==0,cal[field] ,
(nIndices[field]==0||!NumericQ[nIndices[field]])&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}].(cal[field]),
nIndices[field]!= 0&&nder==0, Subscript[cal[field], Sequence@@List[indMod]],
nIndices[field]!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[indMod][[i]]],{i,nder}].(Subscript[cal[field], Sequence@@List[indMod][[nder+1;;nder+nIndices[field]]]])])

Clear[readableIndex]
readableIndex[index_] := index /. {i_Symbol[n_Integer] :> ToString[i] <> ToString[n]}



(* ::Input:: *)
(*Clear[seeReturn]*)
(*seeReturn[expr_]:=expr//readableNotation//TableForm;*)
(**)
(*Clear[see]*)
(*see[expr_]:=expr//EchoFunction[seeReturn]*)
(**)


(* ::Subsubsection::Closed:: *)
(*Show changed and unchanged elements in list *)


(* ::Input:: *)
(*Clear[seeChangedElements]*)
(*seeChangedElements[list1_,list2_]:=Module[{dif={},number=1},*)
(*If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];*)
(*Do[If[list1[[i]]=!=list2[[i]],AppendTo[dif,{number++,i,list1[[i]],list2[[i]]}],{}],*)
(*{i,Length[list1]}];*)
(*Print[Length[dif],"  changes"];*)
(*Print["|\[NumberSign]| Position | list1 | list2 |"];*)
(*dif//see]*)
(**)
(*seeChangedElements[list1_,list2_, a_?IntegerQ]:=seeChangedElements[list1,list2][[1]][[1;;a]]//TableForm*)
(**)
(*Clear[seeEqualElements]*)
(*seeEqualElements[list1_,list2_]:=Module[{dif={},number=1},*)
(*If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];*)
(*Do[If[list1[[i]]===list2[[i]],AppendTo[dif,{number++,i,list1[[i]],list2[[i]]}],{}],*)
(*{i,Length[list1]}];*)
(*Print[Length[dif],"  equal elements"];*)
(*Print["|\[NumberSign]| Position | list1 | list2 |"];*)
(*dif//see]*)
(**)
(*seeEqualElements[list1_,list2_, a_?IntegerQ]:=seeEqualElements[list1,list2][[1]][[1;;a]]//TableForm*)
(**)
(*(* Range[10,20];*)
(*seeChangedElements[%,%//Map[If[EvenQ[#],0,#]&]]*)
(*seeEqualElements[%%,%%//Map[If[EvenQ[#],0,#]&]]*)*)
(**)


(* ::Subsubsection::Closed:: *)
(*Get positions of duplicates*)


(* ::Input:: *)
(*positionDuplicates[list_]:=GatherBy[Range@Length[list],list[[#]]&]*)


(* ::Input:: *)
(*(*example={a,a,b,a,b,c,d};*)
(*positionDuplicates[example]*)
(*%//Cases[#,{_,__}]&*)
(*Length[%]*)
(*Print["With 2 rep: ",Count[%%,{_,_}]]*)
(*Print["With 3 rep: ",Count[%%%,{_,_,_}]]*)
(*Print["With 4 rep: ",Count[%%%%,{_,_,_,_}]]*)*)


(* ::Subsubsubsection::Closed:: *)
(**)


(* ::Input:: *)
(*Clear[compareDuplicates]*)
(*compareDuplicates[list1_,list2_]:=Module[{posd1,posd2,posd},*)
(*If[Length[list1]!=Length[list2],Print["Different Lengths!"];Return[999999]];*)
(**)
(*posd1=positionDuplicates[list1]//Cases[{_,_}];*)
(*posd2=positionDuplicates[list2]//Cases[{_,_}];*)
(**)
(*posd=Complement[posd2,posd1];*)
(*Print[Length[posd]," duplicates found only in 2nd argument:"];*)
(**)
(*Map[list1[[#]]&,posd]//Flatten//see*)
(*]*)


(* ::Subsubsubsection::Closed:: *)
(*How to see the duplicates produced by two versions of a function*)


(* ::Input:: *)
(*(*runs only at the end of 'Reduce with trivial relations'*)*)
(**)
(*(*new=base2//Map[reOrderJSymCases];*)
(*old=base2//Map[reOrderJSymCasesOLD];*)
(**)
(*newDup=new//positionDuplicates//Cases[{_,__}];*)
(*oldDup=old//positionDuplicates//Cases[{_,__}];*)
(**)
(*posJSym=Complement[newDup,oldDup];*)
(**)
(**)
(*Map[new[[#]]&,posJSym]//see*)
(*Map[old[[#]]&,posJSym]//see*)*)


(* ::Subsubsection::Closed:: *)
(*Search terms by field content*)


(* ::Input:: *)
(*Clear[find,findExact]*)
(*find[fields__][terms_List]:=Module[{tally=Tally[{fields}]},*)
(*Select[terms,(And@@Table[Count[#,DD[tally[[i,1]],_][___],99]>=1,{i,Length[tally]}])& ]]*)
(**)
(*findExact[fields__]:=Module[{tally=Tally[{fields}]},*)
(*Select[#,(And@@Table[Count[#,DD[tally[[i,1]],_][___],99]==tally[[i,2]],{i,Length[tally]}])& ]&]*)
(**)
(*Clear[findWithNDer]*)
(*findWithNDer[field_,nder_][terms_List]:=Module[{},*)
(*Select[terms,*)
(*((Count[#,DD[field,nder][___],99]>=1)&)*)
(* ]*)
(*]*)
(**)
(*Clear[findWithMinNDer]*)
(*findWithMinNDer[field_,nder_][terms_List]:=Module[{},*)
(*Select[terms,*)
(*((Count[#,DD[field,_?(#>=nder&)][___],99]>=1)&)*)
(* ]*)
(*]*)
(**)
(**)
(*find::usage="find[fields__][terms_List] returns the terms that contain at least one instance of each of the fields";*)
(*findExact::usage = "findExact[fields__][terms_List] returns the terms that contain these fields, accounting for repetitions, and possibly some other field different than those in the argument";*)
(*findWithNDer::usage = "findWithNDer[field_,nder_][terms_List] will find the terms that contain at least one instance of the field with *exactly* nder covariant derivatives. Alternatives may be given as field1 | field2 | field3";*)
(*findWithMinNDer::usage = "findWithMinNDer[field_,nder_][terms_List] will find the terms that contain at least one instance of the field with *at least* nder covariant derivatives attached to it. Alternatives may be given as field1 | field2 | field3";*)
(**)
(*(*lag//find[chim, fm]//see  (*At least one of each*)*)
(*lag//findExact[chim, fm, fm]//see (*Exactly one chim and two fm*)*)
(*lag //findWithNDer[chim,4]//see (*At least one chim with 4 der*)*)
(*lag//findWithMinNDer[chim,1]//see (*At least one chim with at list 1 der*)*)*)
(**)


(* ::Section::Closed:: *)
(*[Functions] Compose terms*)


(* ::Subsection::Closed:: *)
(*Build terms*)


(* ::Subsubsection::Closed:: *)
(*Get Combinations*)


(* ::Text:: *)
(*getCombinations of 2,...,m building blocks.*)


(* ::Input:: *)
(*(*https://mathematica.stackexchange.com/questions/276141/working-with-tables-add-new-level-of-nested-tables*)*)
(**)
(*Clear[getCombinations]*)
(*getCombinations[factors_,m_Integer]:=Module[{list,  n=Length[factors]},*)
(*list=FrobeniusSolve[ConstantArray[1,n],m];*)
(*Inner[Power,factors,#,Times]&/@list//Sort]*)
(**)
(**)
(*getCombinations::usage = "getCombinations[list_,n_] generates the possible combinations of n elemens in the list";*)
(**)


(* ::Subsubsection::Closed:: *)
(*Apply derivatives and permutations*)


(* ::Text:: *)
(*Get list of fields. Compute all fieldPermutations. Possible combinations of nder derivatives over nfields. Introduce derivatives as DD[f,1]. Freeze ordering with Dot.*)


(* ::Input:: *)
(*Clear[applyDerivativesAndPermutations]*)
(*applyDerivativesAndPermutations[term_]:=Module[{termaux,fields,fieldPermutations,nder,nfields,combinatoricsOfD},*)
(*nder=Exponent[term,der];*)
(*termaux=term/.der->1;*)
(*fields=(termaux/.Times->List/.Power->(Table[#,#2]&))//If[Head[#]=!=List,List[#],#]& //Flatten;*)
(*fieldPermutations=fields//Permutations;*)
(*nfields=Length[fields];*)
(**)
(*combinatoricsOfD=FrobeniusSolve[Table[1,nfields],nder];*)
(**)
(*Inner[ReverseApplied[DD],combinatoricsOfD,#,Dot]&/@fieldPermutations//Flatten*)
(*]*)
(**)
(*applyDerivativesAndPermutations::usage = "applyDerivativesAndPermutations[term_] returns all possible orderings of the fields in term, freezing the order with Dot. Also distributes the n derivatives (der^n) among them. Transforms notation as field -> DD[field,n]";*)


(* ::Subsubsection::Closed:: *)
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



(* ::Input:: *)
(*Clear[applyDistributedOLD]*)
(*applyDistributedOLD[func_,x_]:=Module[{list=If[Head[x]===Dot,List@@x,List[x]],aux},*)
(*aux=Apply[Join,Permutations/@IntegerPartitions[Length[list]]];*)
(*aux=Internal`PartitionRagged[list,#]&/@aux;*)
(*aux=Apply[func,aux,{2}];*)
(*Times@@@aux (*Times: traces commute*)]*)
(**)


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


(* ::Subsubsection::Closed:: *)
(*Re-build function [OLD]*)


(*list={a,b,c,d,e};
func=F;

(aux=Internal`PartitionRagged[list,#]&/@partitionSchemesForXElem[Length[list]];
aux=Apply[func,aux,{2}];
Times@@@aux)//RuntimeTools`Profile*)


(*partitionSchemesForXElem[Length[list]]//RuntimeTools`Profile*)


(* ::Subsection::Closed:: *)
(*Index business*)


(* ::Subsubsection::Closed:: *)
(*Create all index permutations*)


(* ::Input:: *)
(*Clear[generateIndexOrderings]*)
(*generateIndexOrderings[epsilonIndices_,{}]:={epsilonIndices}*)
(*generateIndexOrderings[epsilonIndices_,pairIndices_/;Length[pairIndices]>=1]:=Module[{nPairs,nSingles,indexPermutations,positionPairs,newlist},*)
(**)
(*nPairs=Length[pairIndices];*)
(*nSingles=Length[epsilonIndices];*)
(**)
(*indexPermutations=Permutations[Join[pairIndices,pairIndices]]//Cases[#,{pairIndices[[1]],___}]&;*)
(*positionPairs=Subsets[Range[2*nPairs+nSingles],{2*nPairs}];*)
(**)
(*newlist=Table[{},{j,Length[positionPairs]},{i,Length[indexPermutations]}];*)
(**)
(*Do[*)
(*newlist[[kk]][[jj]]=epsilonIndices;*)
(*Do[newlist[[kk]][[jj]]=Insert[newlist[[kk]][[jj]],indexPermutations[[jj]][[ii]],positionPairs[[kk]][[ii]]],{ii,1,2*nPairs}],{kk,1,Length[positionPairs]},{jj,1,Length[indexPermutations]}];*)
(*Flatten[newlist,{1,2}]*)
(*]*)
(**)
(*generateIndexOrderings::usage = "generateIndexOrderings[epsilonIndices_List,pairIndices_List] returns all possible permutations of the indices. The epsilonIndices have a single instance per term (contracted to something external) and are kept in the order they are given. Instead, pairIndices appear twice per term (contracted) and they are are inserted in all possible ways between the epsilonIndices. In the resulting terms, the first pairIndex is always pairIndices[[1]] (dummy index)";*)
(**)


(* ::Subsubsection::Closed:: *)
(*Index place holders*)


Clear[insertIndexPlaceHolders]
insertIndexPlaceHolders[expr_]:= expr/.DD[field_,nder_]:>DD[field,nder][index[nder+nIndices[field]]]

insertIndexPlaceHolders::usage=
"insertIndexPlaceHolders[expr_] will insert place holders with the total number of indices that are needed 
in each field. Transforms the notation as 
DD[field,nder] -> DD[field,nder][index[m]].
Needs to know how many indices are carried by each field. Define nIndices[field] beforehand in the configuration
(done automatically inside the BB deffinition in the examples)";


(* ::Subsubsection::Closed:: *)
(*Insert one set of indices*)


(* ::Input:: *)
(*Clear[insertOneIndexCombination]*)
(*insertOneIndexCombination[expr_,indices_List]:=Block[{aux,pos,indPerSlot,start,end,rule},*)
(*aux=expr//inactivePower;*)
(**)
(*(*find position of index[n] in expression*)*)
(*pos=Position[aux,index[_Integer]];*)
(**)
(*(*determine the first (start) and last (end) element of indices_List that goes in each place holder*)*)
(*indPerSlot=Extract[aux,pos]/.index[n_]:>n;*)
(*end=Accumulate[indPerSlot];*)
(*start=1+Drop[Insert[end,0,1],-1];*)
(**)
(*(*replace place holders by the indices*)*)
(*rule=Table[pos[[i]]->Sequence@@indices[[start[[i]];;end[[i]]]],{i,Length[pos]}];*)
(*ReplacePart[aux,rule]//Activate*)
(*]*)
(**)
(*insertOneIndexCombination::usage = "insertOneIndexCombination[expr_,indices_List] introduces n indices, in the notation specified in indices_List, in place of index[n], sequentally adds the rest of indices in all index[m].";*)


(* ::Subsubsection::Closed:: *)
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


(* ::Section::Closed:: *)
(*[Functions] Trivial relations*)


(* ::Subsection::Closed:: *)
(*sortTracesBare: order arguments in traces with MMA ordering*)


(* ::Input:: *)
(*Clear[cyclicSortBare,sortTracesBare]*)
(*cyclicSortBare[TR[]]:=TR[];*)
(*(*cyclicSortBare[TR[args__]]:=RotateLeft[TR[args],Ordering[{args},1]-1]*)*)
(*cyclicSortBare[TR[args__]]:=Module[{aux={args}, extraRot},*)
(*aux=RotateLeft[aux,Ordering[aux,1]-1];*)
(**)
(*(*first = last. Only 2 identicals possible (2 j1s)*)*)
(*If[Order@@aux[[{1,-1}]]==0,aux=RotateRight[aux],{}]; *)
(**)
(*(*Cases {a_,b__,a_,c__}*)*)
(*(*Length of b & c must be equal since this function is only to find symmetric cases*)*)
(*If[EvenQ[Length[aux]]&&MatchQ[aux,{a_,b__,a_,c__}],{},Return[TR@@aux]];*)
(*aux/.{a_,b__,a_,c__}:>If[Order[{b},{c}]==-1,aux=RotateLeft[aux,1+Length[{b}]],aux];*)
(**)
(*TR@@aux]*)
(**)
(*Clear[sortTracesBare]*)
(*sortTracesBare[expr_]:=expr/.TR[a__]:> cyclicSortBare[TR[a]];*)
(*(*TR[11,3,99,7]TR[b,a,c]//sortTracesBare*)*)


(* ::Subsection::Closed:: *)
(*ignoreSigns / addSigns / deleteDuplicatesSign: deal with signs*)


(* ::Input:: *)
(*Clear[pullSign]*)
(*pullSign[expr_]:=expr//.TR[a___,sign x_,b___]:>sign TR[a,x,b]*)
(**)
(*(*sign TR[DD[fm,0][j1,m1],DD[fm,0][j2,j1],sign DD[fp,0][j2,m2],DD[u,1][m3,m4]]*)
(*%//pullSign*)*)


(* ::Input:: *)
(*Clear[ignoreSigns]*)
(*ignoreSigns[expr_]:=expr/.sign->1*)


(* ::Input:: *)
(*Clear[addSigns]*)
(*addSigns[expr_]:=expr/.sign->-1*)


(* ::Input:: *)
(*Clear[simplifySign]*)
(*simplifySign[expr_]:=expr/.{sign^2->1,sign^3->sign,sign^4->1,sign^5->sign,sign^6->1,sign^7->sign}*)


(* ::Subsubsection::Closed:: *)
(*Delete signed duplicates*)


(* ::Text:: *)
(*We look at the sign of the first element. And if its negative, flip the sign of the whole expression with flipSigns.*)
(*Then DeleteDuplicates*)


(* ::Input:: *)
(*Clear[deleteDuplicatesSign]*)
(*deleteDuplicatesSign[list_]:=Map[flipSigns,list]//DeleteDuplicates*)
(**)
(*Clear[flipSigns]*)
(*flipSigns[expr_Times]:= Module[{needsSign=False},*)
(*expr/.Times[_?Negative,z___]:>(needsSign=True;0);*)
(*If[needsSign,- expr, expr]*)
(*]*)
(*flipSigns[expr_Plus]:=Module[{needsSign=False},*)
(*expr/.Plus[x_,y___]:>*)
(*(x/.Times[_?Negative,z___]:>(needsSign=True;0));*)
(*If[needsSign,- expr, expr]*)
(*]*)
(*flipSigns[expr_?((Head[#]=!=Plus)&&(Head[#]=!=Times)&&(Head[#]=!=List)&)]:= expr*)
(*flipSigns[expr_List]:=Map[flipSigns,expr]*)
(**)
(*(*{a*b -c*d, -b*f,a*b+c*d,c*d-a*b}*)
(*%//deleteDuplicatesSign*)
(**)
(*-TR[DD[fm,0][m1,m2],DD[fp,1][j1,j2,m3],DD[u,0][j1],DD[u,1][j2,m4]]+TR[DD[fm,0][m1,m2],DD[fp,1][j1,j2,m3],DD[u,1][j2,j1],DD[u,0][m4]];*)
(*{%,%//flipSigns}//see*)*)


(* ::Subsection::Closed:: *)
(*Apply function on the terms*)


(* ::Input:: *)
(*Clear[onTerms]*)
(*onTerms[F_][expr_]:=Distribute[Hold[F][Expand[expr]]]//ReleaseHold*)
(**)
(*(*TR[DD[chim,0][]] TR[DD[chip,0][]] TR[DD[fm,0][m1,m2],DD[u,1][m3,m4]]+8TR[DD[chim,1][m1]] TR[DD[chip,0][]] TR[DD[fm,0][m2,m3],DD[u,0][m4]];*)
(*{%,%//onTerms[APPLY]}//see*)*)


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


(* ::Subsection:: *)
(*Identify terms; orderFields; getTraceScore*)


Clear[orderFields]
orderFields[expr_?(Head@Head@#===DD&)]:=expr/.DD[f_,n_][ind___]:>(Switch[f, fa,10+n, fb,20+n, fc,30+n])

orderFields::usage = "orderFields[expr_] is a user-defined function. It is the core function that defines the importance 
of each field in the terms. Other functions that directly or indirectly depend on it are:
 - general miniBASIS functions: getTraceScore, termScore, makeIdentifyTerms
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


(* ::Input:: *)
(*Clear[removeOverallFactor]*)
(*removeOverallFactor[expr_]:=expr//FactorTerms//Replace[#,Times[_?NumericQ,rest_]:>rest]&*)
(**)
(*Clear[removeOverallFactorReal]*)
(*removeOverallFactorReal[expr_]:=expr//FactorTerms//Replace[#,Times[f_?(#\[Element]Reals &),rest_]:>rest]& //Replace[#,Times[f:Complex[a_,b_?(#!=0&)] , rest_]:>(f/b)rest ]&*)
(*(*This removes the real overall factor, or if it is complex, leaves the imaginary part = 1*)*)
(**)
(**)
(*(*Homemade version*)*)
(*Clear[relWithIntegers]*)
(*relWithIntegers[expr_]:=Module[{aux,maxFactor},*)
(*aux=Cases[expr,Rational[_,n_]:>n,99];*)
(*If[aux==={},Return[expr],{}];*)
(*maxFactor=Max[aux];*)
(*maxFactor*expr//Distribute*)
(*]*)
(**)
(*Clear[cleanTraces]*)
(*cleanTraces[expr_]:=Module[{aux=expr},*)
(*aux=aux/.TR[A___]:>Map[Expand,TR[A]];*)
(*aux=aux//.TR[A___,a_+b_+c_,B___]:>TR[A,a,B]+TR[A,b,B]+TR[A,c,B];*)
(*aux=aux//.TR[A___,a_+b_,B___]:>TR[A,a,B]+TR[A,b,B];*)
(*aux=aux//.TR[A___,a_+2 b_,B___]:>TR[A,a,B]+2 TR[A,b,B];*)
(*aux=aux//.TR[A___,a_TR,B__]:>a TR[A,B]; (*A can be empty, not B*)*)
(*aux=aux//.TR[A__,a_TR,B___]:>a TR[A,B]; (*viceversa*)*)
(*aux=aux//.TR[TR[a__]]:>Nf TR[a]; (*Both empty: Nf factor*)*)
(*aux=aux//.TR[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)DD[x__] [y___],B___]:>n TR[A,DD[x][y],B];*)
(*aux=aux//.TR[A___,n_?(Head[#]=!=DD[__]&&Head[#]=!=seq&)seq[x__],B___]:>n TR[A,seq[x],B];*)
(*aux=aux//.TR[A___,seq[x__],B___]:>TR[A,Sequence[x],B];*)
(*aux=aux//.TR[A___,{x__},B___]:>TR[A,Sequence[x],B]*)
(**)
(*]*)
(**)
(**)


(* ::Subsection::Closed:: *)
(*checkRule: check user-defined identities*)


Clear[checkRule]
checkRule[tag_,rule_]:=Module[{},
If[(rule[[1]]/.tagX:>firstHead[tag[dummy][[1]]])=!=(tag[dummy][[1]]//removeDollarSign), 
Print["WARNING: tag and rule should have identical LHS except for the headers: tagX and DD"]];
(rule[[1]]/.tagX->firstHead[tag[dummy][[1]]]//removePatterns) -> ((rule[[1]]//removePatterns) /.rule )//see
]

Clear[firstHead]
firstHead[expr__] := If[Length[{expr}]>1,seq,firstHead[expr]]
firstHead[expr_] := If[Length[{expr}]>1,seq,NestList[Head,expr,5]//#[[FirstPosition[#,Symbol][[1]]-1]]&]

checkRule::usage "checkRule[tag_,rule_] checks that the tag will only be placed on the terms where the rule applies. 
It also prints the rule nicely formatted to help in its writing";


Clear[removeDollarSign]
removeDollarSign[expr_]:=expr//FullForm//ToString//StringReplace["$"->""]//ToExpression

Clear[removePatterns]
removePatterns[expr_] := expr /.
Verbatim[Pattern][_,Verbatim[BlankNullSequence][]]:>Sequence[] /.
Verbatim[PatternTest][sym_,test_]:>(k=0;While[!test[k] && k!=99,k++];
If[k==99, Print["ERROR: Sorry, I can't check. Your PatternTest is too complicated for me"];Abort[]];k) /. 
Verbatim[Pattern][sym_,___]:>sym



(* ::Subsection::Closed:: *)
(*getRelationsFromRule: find operator relations from user-defined identities*)


(* ::Text:: *)
(*This function finds all ocurrences of tag in each term, and duplicates the term as many times as necessary to have only one insertion of the rule in each place.*)
(**)
(*Since in our initial basis there are never more than 3 traces*, or more than 3 occurrences of the expression we are looking for, we only define tag1,tag2,tag3*)
(**check with: lag/.TR[a___]:>AA//Tally*)
(**)


(* ::Input:: *)
(*Clear[getRelationsFromRule]*)
(*getRelationsFromRule[lag_List,rule_,tag_,head_]:=Module[{lagTagged,allInsertions,tmpLag},*)
(*lagTagged=ConstantArray[0,Length[lag]];*)
(**)
(*tmpLag=lag;*)
(*lagTagged=Map[(i=0;#/.tag[tag1])&,tmpLag]; *)
(**)
(*tmpLag=lagTagged;*)
(*lagTagged=Map[(i=0;#/.tag[tag2])&,tmpLag]; *)
(**)
(*tmpLag=lagTagged;*)
(*lagTagged=Map[(i=0;#/.tag[tag3])&,tmpLag]; *)
(**)
(**)
(**)
(*lagTagged=Join[*)
(*lagTagged/.{tag1->tagX,tag2->head,tag3->head},*)
(*lagTagged/.{tag1->head,tag2->tagX,tag3->head},*)
(*lagTagged/.{tag1->head,tag2->head,tag3->tagX}];*)
(**)
(*lagTagged=Select[lagTagged,!FreeQ[#,tagX[__]]&];*)
(**)
(*allInsertions=lagTagged/.rule//Flatten;*)
(*Print[allInsertions//Length, " relations found"];*)
(*allInsertions//cleanTraces//Map[Distribute]*)
(**)
(*]*)
(**)
(**)
(*getRelationsFromRule::usage = *)
(*"getRelationsFromRule[lag_List,rule_,tag_,head_] finds all the relations between operators in lag based on one identity.*)
(**)
(* - rule econdes the identity. If f[A]+f[B]+f[C]=0, we should write rule = (tagX[A] -> f[A]+f[B]+f[C]). If some of the terms involved in the identity may be zero in some cases because of index antisymmetries, it is safer to insert the relation through all terms. Call again getRelationsFromRule, now with rule = (tagX[B] -> f[A]+f[B]+f[C])*)
(* - tag encodes the LHS of rule. The tag must include at the end '/; i++<1'. In the examples above, it should be tag = (tagFunction[tag_] := f[A]->tag[A]/; i++<1)*)
(* - head is the Head of the LHS of rule (usually TR or DD). In the example above head = f*)
(*";*)
(**)
(*(*ruleTEST=tagX[u,n_][ind___,a_,a_]:>DD[u,n][ind,a,a] -(1/2)ii DD[chim,n-1][ind]+TR[(1/Nf)ii DD[chim,n-1][ind]];*)
(*tagTEST[DDtag_]:=DD[u,n_][ind___,a_,a_]:>DDtag[u,n][ind,a,a] /;i++<1;*)
(**)
(*fullTEST=getRelationsFromRule[lag[[1;;1000]],ruleTEST,tagTEST,DD]//showTiming;*)
(*%//see*)*)
(**)


(* ::Subsubsection::Closed:: *)
(*Faster getRelationsFromRuleFast [REMOVE]*)


(* ::Text:: *)
(*The bottleneck is in cleanTraces, so this (simpler) code improves the overall speed only by 20%. But cannot be used for head !=DD*)


Clear[getRelationsFromRuleFast]
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



(*getRelationsFromRule[lag[[1;;2]],ruleFMUt,tagFMUtc,DD]//showTiming;
getRelationsFromRuleFast[lag[[1;;2]],ruleFMUt,tagFMUtc,DD]//showTiming;*)


(* ::Subsection::Closed:: *)
(*rotateTraces: generate all orderings of the traces *)


(* ::Input:: *)
(*Clear[rotateTraces]*)
(*rotateTraces[lag_]:=Module[{rotatedlag=ConstantArray[0,8],newlag},*)
(*Do[*)
(*rotatedlag[[nrot]]=lag/.TR[arg__]:>TR[Sequence@@RotateLeft[{arg},nrot]]/;Length[{arg}]>nrot;*)
(*,{nrot, 8}];*)
(**)
(*newlag=rotatedlag//Flatten//DeleteDuplicates;*)
(*Print["Expanded basis with all rotations of the traces: ", Length[lag], " \[RightArrow] ",Length[newlag], " terms"];*)
(*newlag*)
(*]*)
(**)
(*(*rotateTraces[lag];*)*)
(**)


(* ::Subsection::Closed:: *)
(*Helpers to debug - findLinearlyDependent, findSameOperators*)


(* ::Input:: *)
(*Clear[justOpes,findLinearlyDependent,findSameOperators]*)
(*justOpes[expr_]:=(expr//plusToList)//.x_. ope[xx_]:>ope[xx]/.- ope[a_]->ope[a];*)
(*findLinearlyDependent[list_]:= Gather[list,IntersectingQ[#1//justOpes,#2//justOpes]&]//Cases[{_,__}];*)
(*findSameOperators[list_]:=GroupBy[list,#//.x_. ope[xx_]:>ope[xx] //.x_. ope[xx_] + y_. ope[yy_]:>ope[xx*yy ]&]//Cases[{_,__}];*)


(* ::Input:: *)
(*(*{{ope[1601]+ope[1656]+ope[1722]+ope[1723],ope[1601]+ope[1656]-ope[1722]-ope[1723]},{ 1/2 ii ope[1601]-ope[10241]+ope[10243]+ope[10532]+ope[10533],ope[10239]-ope[10241]+ope[10243]-ope[10532]-ope[10533]},{ope[11901]-ope[11903]+ope[11905]+ope[12194]+ope[12195],ope[11901]-ope[11903]+ope[11905]-ope[12194]-ope[12195]}};*)
(*%//Flatten;*)
(*%//findSameOperators//TableForm*)
(*%%//findLinearlyDependent//TableForm*)*)


(* ::Subsection::Closed:: *)
(*Cayley-Hamilton [CH]*)


(* ::Text:: *)
(*Helper functions to extract operator relations from Cayley-Hamilton trace relations*)
(**)
(*Group the arguments of each TR into nf Lists in all possible ways. Allow also any leftover arguments at the end.*)


Clear[separateArgsTR]
separateArgsTR[nf_][expr_]:=Module[{listArgs,npart},
expr/.TR[a___]:>(listArgs={a};
If[Length[listArgs]<nf,
TR[a],
Total[TR@@@Join[
Internal`PartitionRagged[listArgs,#]&/@groupTR[Length[listArgs],nf],
Internal`PartitionRagged[listArgs,#]&/@groupTR[Length[listArgs],nf+1]//Map[#/.{first__,last_}:>{first,Sequence@@last}&]
]]]
)//Expand
]

(*TR[a,b,c,d]TR[G,H]//separateArgsTR[3]//TableForm*)


(* ::Text:: *)
(*Pre-calculate grouping schemes for a list of length len and npart subgroups. Store results in the symbols groupTR[len,npart]*)


(*groupTR = partitionSchemesForNElemInMGroups*)

Do[Do[
groupTR[len,npart]=Apply[Join,Permutations/@Select[IntegerPartitions[len],Length[#]==npart&]];
,{len,8}],{npart,8}]


(* ::Text:: *)
(*Function to sort the matrices inside a group to avoid creating duplicate relations*)


Clear[sortGroupsCH]
sortGroupsCH[lagWithGroups_]:=lagWithGroups/.TR[arg__List]:>TR[Sequence@@Sort[{arg}]]/.TR[arg__List,leftover__?(Head[#]=!=List&)]:>TR[Sequence@@Sort[{arg}],leftover]


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


Clear[getRelationSCH4m]
getRelationSCH4m[term_]:=Module[{aux=term,posM,posJ,pos5,ind5},

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
inverseRules[[i]]=MapThread[Rule,{opesInSubset,Inverse[submatrix].opesInSubset}];
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
Print["Creating matrix from ",Length[aux//Flatten]," relations..."];

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
"getRelationMatrix[list__] returns a SparseArray encoding all the monomial relations. These are supplied as a list of
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
(*Get Basis [SuiteSparseQR]*)


Clear[getMinimalBasis]
getMinimalBasis[A_SparseArray]:=Module[{matrixPath,cmdCompile,cmdRun,env,stdout,diag,basis, D,P},

Print["Factorising ...\n"];

(*Save matrix; compile; run SPQR with matrix as argument*)
Quiet@CreateDirectory[NotebookDirectory[]<>"tmp"];
matrixPath=Export[NotebookDirectory[]<>"tmp/mat.mtx",A];
cmdCompile="g++ "<>NotebookDirectory[]<>"SPQR/decQR.cpp "<>"-lcholmod -lspqr -lsuitesparseconfig -o "<>NotebookDirectory[]<>"tmp/tmp"; 
cmdRun=NotebookDirectory[]<>"tmp/tmp "<>matrixPath; 
Print[cmdRun];

(*env=<|"LD_LIBRARY_PATH"->"/home/etlar/joan/Programs/SuiteSparse-7.0.1/CHOLMOD/build:$LD_LIBRARY_PATH"|>;*)
env=<|"LD_LIBRARY_PATH"->"/home/joanruiz/Programs/SuiteSparse-7.0.1/lib:$LD_LIBRARY_PATH"|>;
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,"StandardOutput",cmdRun,ProcessEnvironment->env];
stdout//Print;

(*RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,"StandardOutput",cmdRun,ProcessEnvironment->env];
stdout//Print;*)

D=Import[NotebookDirectory[]<>"tmp/matOutD.mtx"];
P=ReadList[NotebookDirectory[]<>"tmp/permOut.txt",Number] + 1; (*correct 0-based vector*)

{D,P}=Chop[{D,P}];

diag=Table[D[[i,i]],{i,Min[Dimensions[D]]}];
basis=Position[diag[[Ordering[P]]],0]//Map[#/.{n_}->ope[n]&];

Print["Minimal basis obtained:  ", Length[basis], " operators altogether"];

basis

]

getMinimalBasis::usage =
"getMinimalBasis[A_SparseArray] performs the reduction to a minimal basis of operators based on the relations 
found between monomials, which are given as input through the SparseArray A, generated by getRelationMatrix";



(* ::Subsection::Closed:: *)
(*Get Rank [SuiteSparseQR]*)


(* ::Text:: *)
(*  - getRank: Uses SparseQR. Performs QR decomposition, where R is upper triangular. Rank is the number of nonzero elements in the diagonal. Needs installation of SuiteSparse and its dependencies. Get it running first in C++. This is faster than getMinimalBasis because we don't impose preferred operators*)
(*  - getRankMathematicaQuick = SparseMatrixRank (stackexchange) = LinearSolve::Multifrontal = UMFPACK: Built in Mathematica. Uses fast LU decomposition. But generally fails with large singular matrices*)
(* - getRankMathematica = RRMCF. Basic LU decomposition. Slow. Not optimized for sparse matrices. Gives the correct answer. Explicit algorithm explained in https://www.sciencedirect.com/science/article/pii/S0024379506002011 *)
(**)
(* Getting the rank of a large matrix in Mathematica isn't straightforward. I explained the situation in https://mathematica.stackexchange.com/questions/283946/rank-of-singular-large-sparse-matrices*)


(* ::Subsubsubsection::Closed:: *)
(*SuiteSparseQR*)


Clear[getRank]
getRank[A_SparseArray]:=Module[{matrixPath,cmdCompile,cmdRun,env,stdout,rank,navariables},
(*Save matrix; compile; run SPQR with matrix as argument*)
Quiet@CreateDirectory[NotebookDirectory[]<>"tmp"];
matrixPath=Export[NotebookDirectory[]<>"tmp/mat.mtx",A];
cmdCompile="g++ "<>NotebookDirectory[]<>"SPQR/rankQR.cpp "<>"-lcholmod -lspqr -lsuitesparseconfig -o "<>NotebookDirectory[]<>"tmp/tmp"; 
cmdRun=NotebookDirectory[]<>"tmp/tmp "<>matrixPath; 

(*env=<|"LD_LIBRARY_PATH"->"/home/etlar/joan/Programs/SuiteSparse-7.0.1/CHOLMOD/build:$LD_LIBRARY_PATH"|>;*)
env=<|"LD_LIBRARY_PATH"->"/home/joanruiz/Programs/SuiteSparse-7.0.1/lib:$LD_LIBRARY_PATH"|>;
RunProcess[{$SystemShell,"-c",cmdCompile},"StandardError"]//Print;
stdout=RunProcess[$SystemShell,"StandardOutput",cmdRun,ProcessEnvironment->env];
stdout//Print;
rank=stdout//StringTake[#,-10]&//ToExpression;

nvariables = First[Dimensions[A] ];

Print["Nbr. of monomials: ", nvariables ];
Print["Nbr. of independent relations (rank): ",rank];
Print["Nbr. of independent monomials: ", nvariables-rank];

rank
]

getRank::usage = 
"getRank[A_SparseArray] returns the rank of the matrix A. This is the number of independent relations, 
each of which removes one operator from the basis. Needs installation of SuiteSparseQR and its dependencies.
";


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
If[A!=L.U, Print["getRankMathematica FAILED with this matrix. Use getRankMathematicaQuick or getRank (needs SuiteSparseQR)"];Return[Null]];

nvariables=m;
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


If[(L.U)[[p,q]]!=a, Print["getRankMathematicQuick FAILED with this matrix. Use getRankMathematica or getRank (needs SuiteSparseQR)"];Return[Null]];

rank = Total[Unitize[Diagonal[Chop[U]]]];
nvariables = First[Dimensions[A] ];

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
"getRankMathematica[A_SparseArray] returns the rank of the matrix A. This is the number of independent relations, each of which removes one operator from the basis. It uses a rank-revealing algorithm of LU decomposition.

For near-square relation matrices this (undocumented Mathematica function) works (slightly) faster,
p = relationMatrix//toSquare//SparseArray`ApproximateMinimumDegree[#]&; (*Re-order rows before doing the decomposition*)
relationMatrix[[All,p]]//getRankMathematica
";

getRankMathematicaQuick::usage = 
"getRankMathematicaQuick[A_SparseArray] returns the rank of the matrix A. 
Uses the UMFPACK algorithm through the Mathematica built-in functon LinearSolve::Multifrontal.
May fail for large singular matrices";




(*n=3000; (*Increase to induce fail*)
d2=1000;
d1=600;
i=RandomInteger[{1,d1},n];
j=RandomInteger[{1,d2},n];
v=RandomInteger[{-10,10},n];
sa=SparseArray[Transpose[{i,j}]\[Rule]v,{d1,d2}];

getRank[sa]
getRankMathematicaQuick[sa]
getRankMathematica[sa]

*)


(* ::Input:: *)
(*`*)


(* ::Subsection::Closed:: *)
(*Create basis summary*)


Clear[summary]
summary[basis_,{applySym__},vanishRules___]:=Module[{basisEven,basisSubset,nSymEven},

Print["\nSummary of the final miniBASIS:"];


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


(* ::Input:: *)
(*Clear[summaryOLD]*)
(*summaryOLD[basis_,applySym_,vanishRules___]:=Module[{basisEven,basisSubset,nSymEven},*)
(**)
(*Print["\nSummary of the final miniBASIS:"];*)
(**)
(**)
(*basisEven = basis//Select[signsUnder[applySym][#]==1&];*)
(*nSymEven = basisEven//Length;*)
(*If[nSymEven ==0, *)
(*Print["Could not determine if the terms are even or odd.\n" ];basisEven=basis,*)
(*Print["\n    -",  nSymEven , " even terms \n    -", Length[basis]-nSymEven, " odd terms \n"]*)
(*];*)
(**)
(*Print["All terms     "," - ", Length[basisEven], " terms"];*)
(*i=1;*)
(*Table[*)
(*basisSubset[i] = basisEven/.rule/.TR[___ , DD[0,_][___] , ___]:>0//DeleteCases[0]//DeleteDuplicates;*)
(*Print["Basis subset ",i," - ", Length[basisSubset[i]], " terms"];*)
(*i++;*)
(*,{rule,{vanishRules}}];*)
(**)
(*maxLength = Max[Length/@basisSubset/@Range@Length[{vanishRules}]];*)
(*If[maxLength<= 50, *)
(*Print["\n BASES (specified subsets): "];*)
(*Join[{Range[maxLength]},basisSubset/@Range[Length[{vanishRules}]]]//Transpose@PadRight[#, Automatic, ""]&//TableForm//see;*)
(*];*)
(**)
(*basisEven*)
(*];*)
(**)


(* ::Input:: *)
(*Clear[removeTermsWith]*)
(*removeTermsWith[f__][expr_]:=expr/.TR[___,DD[Alternatives[f],_][___],___]:>0//DeleteCases[0]*)


(* ::Section::Closed:: *)
(*End package*)


(*EndPackage[]*)


(* ::Chapter::Closed:: *)
(*Partial documentation*)


(* ::Text:: *)
(*Reproduction of the documentation written for some of the most relevant functions. Also some examples of use.*)


(* ::Section:: *)
(*[Doc] General helpers*)


?plusToList
a+b-c//plusToList


?inactivePower
a^3 b^4
%//inactivePower
%//Activate


(* ::Section:: *)
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
introduceTraces[{{a.b.c},{X.Y},{Z}}] //TableForm


?insertIndexPlaceHolders
nIndices[chip]=0;
nIndices[fm]=2;
nIndices[fp]=2;
TR[DD[chip,1],DD[fm,2],DD[fp,0]]//insertIndexPlaceHolders


?insertOneIndexCombination
term=F[a][index[1]]*G[b][index[3]]^2
insertOneIndexCombination[term,{j1,j1,m1,m2,m3,m4,m5}]


?generateIndexOrderings
generateIndexOrderings[{a,b},{A}]
generateIndexOrderings[{a},{A,B}]
generateIndexOrderings[{},{A,B}]
generateIndexOrderings[{a,b},{}]


(* ::Section:: *)
(*[Doc] Trivial relations*)


?getDictionaryOfShapes
{{a1,a2},{b1,b2},{X,Y,Z}}
%//Map[getDictionaryOfShapes]


?orderFields
?getTraceScore
?termScore


?makeIdentifyTerms


(* ::Section:: *)
(*[Doc] Operator relations*)


?getRelationsFromRule


(* ::Section:: *)
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


(* ::Section:: *)
(*[Doc] Gaussian Elimination*)


?getRelationMatrix


?getMinimalBasis


?getRank
?getRankMathematica
?getRankMathematicaQuick


(* ::Chapter::Closed:: *)
(*ChPT: anomalous sector. Small-u basis. Order p^6-p^8*)


START=Now;


(* ::Text:: *)
(*Time*)
(*p^6 - 16s*)
(*p^8 - 1h (small RAM, don't know in a proper computer)*)


(* ::Subsection::Closed:: *)
(*Configuration*)


(* ::Subsubsection::Closed:: *)
(*Compose terms (fields,symmetries,indices)*)


(* ::Text:: *)
(*Define the building blocks (BB). Each has a number of indices, p power, and intrinsic parity*)


Clear[BB,clearRegulators]
BB=Module[{fields,pOrder,indices,intParity},

fields = {u, chip,chim,fp,fm,der};
pOrder = {p^1,p^2,p^2,p^2,p^2,p^1};
indices = {in^1,in^0,in^0,in^2,in^2,in^1};
intParity = {ip^1,ip^0,ip^1,ip^0,ip^1,ip^0};

fields*pOrder*indices*intParity];

clearRegulators[exp_]:=exp/.{in->1,p->1,ip->1}


(* ::Text:: *)
(*Write again the number of indices carried by each field*)


Clear[nIndices]
nIndices[chim]=0;
nIndices[chip]=0;
nIndices[fm]=2;
nIndices[fp]=2;
nIndices[u]=1;


(* ::Text:: *)
(*Get combinations of BB specifying which p^n order, number of indices, and if even / odd intrinsic parity*)


Clear[getCombinationsWithSymmetries]
getCombinationsWithSymmetries[order_,nindices_List,ipOddEvenQ_]:=Module[{combs},

combs=Map[getCombinations[BB,#]&,Range[2,8] ]//Flatten;

combs=combs//Cases[#,p^order  _]& ;
combs=combs//Cases[#,in^a_ _/;MemberQ[nindices,a]]&;
combs=combs//Cases[#,all_/;ipOddEvenQ[Exponent[all,ip]]]&//clearRegulators
]


(* ::Text:: *)
(*Indices*)


mIndices={m1,m2,m3,m4};
jIndices={j1,j2};

isM=MemberQ[mIndices,#]&;
isJ=MemberQ[jIndices,#]&;

Clear[nPairs]
nPairs[expr_]:=Which[!FreeQ[expr,j2],2,!FreeQ[expr,j1],1,0==0,0]


(* ::Subsubsection::Closed:: *)
(*Compose terms (insert indices)*)


(* ::Subsubsubsection::Closed:: *)
(*Insert all permutations*)


(* ::Text:: *)
(*Indices to insert when we have only 4 Levi-Civita indices, or +1 pair, or +2 pairs*)


(* ::Input:: *)
(*Clear[indPerm4,indPerm6,indPerm8]*)
(*indPerm4={{m1,m2,m3,m4}};*)
(*indPerm6=generateIndexOrderings[{m1,m2,m3,m4},{j1}];*)
(*indPerm8=generateIndexOrderings[{m1,m2,m3,m4},{j1,j2}];*)


(* ::Input:: *)
(*Clear[insertIndices,nbrOfIndices]*)
(*insertIndices[expr_]:=*)
(*Switch[nbrOfIndices[expr],*)
(*4,insertOneIndexCombination[expr,#]&/@indPerm4,*)
(*6,insertOneIndexCombination[expr,#]&/@indPerm6,*)
(*8,insertOneIndexCombination[expr,#]&/@indPerm8*)
(*]*)
(**)
(*nbrOfIndices[expr_]:=Module[{aux,pos},*)
(*aux=expr//inactivePower;*)
(*Total[Cases[aux,index[n_]->n,99]]*)
(*]*)
(**)
(*(*term=F[a][index[7]]*G[b][index[3]]^2*)
(*nbrOfIndices[term]*)*)


(* ::Subsubsection::Closed:: *)
(*Readable notation*)


Clear[cal]
cal[expr_]:=expr/.{fm:>SuperMinus[\[ScriptF]],fp:>SuperPlus[\[ScriptF]],chim:>SuperMinus[\[Chi]],chip:>SuperPlus[\[Chi]],u:>\[ScriptU]}
(*readableNotation[expr_]:=expr/.DD[field_,nder_][ind___]:>
Which[
(nIndices[field]==0||!NumericQ[nIndices[field]])&&nder==0,cal[field] ,
(nIndices[field]==0||!NumericQ[nIndices[field]])&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[ind][[i]]],{i,nder}].(cal[field]),
nIndices[field]!= 0&&nder==0, Subscript[cal[field], Sequence@@List[ind]],
nIndices[field]!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[ind][[i]]],{i,nder}].(Subscript[cal[field], Sequence@@List[ind][[nder+1;;nder+nIndices[field]]]])]

readableNotationOLD[expr_]:=expr/.DD[field_,nder_][ind___]:>
Which[
nIndices[field]==0&&nder==0,cal[field] ,
nIndices[field]== 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[ind][[i]]],{i,nder}].(cal[field]),
nIndices[field]!= 0&&nder==0, Subscript[cal[field], Sequence@@List[ind]],
nIndices[field]!= 0&&nder!= 0, Dot@@Table[Subscript[\[EmptyDownTriangle],List[ind][[i]]],{i,nder}].(Subscript[cal[field], Sequence@@List[ind][[nder+1;;nder+nIndices[field]]]])]*)


(*To keep ordering when using this function: expr/.Times:>Dot//readableNotation;*)

(*TR[DD[fp,0][a,b]]*TR[DD[chip,0][],DD[chim,2][c,d],DD[fm,0][k,m],DD[u,2][x,y,z]]
%//readableNotation*)


(* ::Subsubsection::Closed:: *)
(*Trivial relations (removeZeroes, generateAlternativeShapes,enhanceWithSimulatedEpsPermutations)*)


(* ::Subsubsubsection::Closed:: *)
(*removeEasyZeroes*)


Clear[removeEasyZeroes]
removeEasyZeroes[expr_]:=Module[{aux=expr},
aux=aux//removeTrU;
aux=If[zeroTrF,aux//removeTrF,aux//removeTrFm];
aux=aux//removeAntisymF]

Clear[removeEasyZeroesOLD]
removeEasyZeroesOLD[expr_]:=Module[{aux=expr},
aux=aux//removeTrU;
aux=If[zeroTrF,aux//removeTrF,aux//removeTrFm];
aux=aux//removeAntisymF]


(* ::Text:: *)
(*removeTrU: Tr[u] = 0*)


Clear[removeTrU]
removeTrU[expr_]:=expr/.TR[DD[u,n_][___]]:>0 
(*TR[DD[fm,0][m1,m2],DD[u,0][m3]] TR[DD[u,0][j1]]TR[DD[u,0][m4],DD[u,0][j1]];
{%,%//removeTrU}//see*)


(* ::Text:: *)
(*removeTrF: Tr[f] = 0*)


Clear[removeTrF,removeTrFm]
removeTrF[expr_]:=expr/.TR[DD[f:(fm|fp),_][__]]:>0
removeTrFm[expr_]:=expr/.TR[DD[fm,_][__]]:>0
(*TR[DD[fm,0][m1,m2]] TR[DD[u,0][j1],DD[u,0][m4],DD[u,0][j1],DD[u,0][m3]];
{%,%//removeTrF}//see*)


(* ::Text:: *)
(*removeAntisymF: f_aa=0*)


Clear[removeAntisymF]
removeAntisymF[expr_]:=expr/.TR[___,DD[f:(fm|fp),n_][___,j_,j_],___]:>0
(*TR[DD[fm,0][j,j],DD[u,0][m1]] TR[DD[u,0][m4],DD[u,0][m2],DD[u,0][m3]];
{%,%//removeAntisymF }//see*)


(* ::Subsubsubsection::Closed:: *)
(*generateAlternativeShapes*)


Clear[generateAlternativeShapesNoEps]
generateAlternativeShapesNoEps[term_]:=Module[{aux=term},
aux=aux//rotationsOfTR;
aux=aux//Map[swapIndicesF]//Flatten;
aux=aux//Map[swapDummyIndices[j1,j2]]//Flatten;
aux=aux/.Times[_?NumericQ,rest__]:>Times[rest];
(*The m indices should be permuted (x4!). It crashes the RAM, so we //ignoreM and //reintroduceM*)
(*aux=aux//Map[shuffleIndicesEps]//Flatten//DeleteDuplicates*)
aux=aux//ignoreSigns;
PrependTo[aux,term] (*Keep the original term in first possition*)
]


Clear[rotationsOfTR,allCyclicRotations]

rotationsOfTR[expr_]:=(expr/.TR[a___]:>(Plus@@allCyclicRotations[TR[a]])//.
TR[a___,x_+y_,b___]:>TR[a,x,b]+TR[a,y,b]//Expand//plusToList)/.Times[_?NumericQ,rest__]:>Times[rest]

allCyclicRotations[expr_]:=Map[RotateRight[expr,#]&,Range[Length[expr]]]

Clear[swapIndicesF]
swapIndicesF[expr_]:=expr/.DD[f:(fm|fp),n_][i___,x_,y_]:>DD[f,n][i,x,y]+sign DD[f,n][i,y,x]/;x=!=y//.TR[a___,x_+y_,b___]:>TR[a,x,b]+TR[a,y,b]//Expand//plusToList;

Clear[swapIndicesFNoSignOLD]
swapIndicesFNoSignOLD[expr_]:=expr/.DD[f:(fm|fp),n_][i___,x_,y_]:>DD[f,n][i,x,y]+DD[f,n][i,y,x]/;x=!=y//.TR[a___,x_+y_,b___]:>TR[a,x,b]+TR[a,y,b]//Expand//plusToList;

Clear[swapDummyIndices]
swapDummyIndices[a_,b_][term_]:=If[!FreeQ[term,b],{term,term/.{a:>b,b:>a}},{term}]

Clear[shuffleIndicesEpsOLD]
shuffleIndicesEpsOLD[expr_]:=Module[{aux=expr,pos,permIndices,permSigns},
pos=Position[expr,_?(isM)];
If[pos=={},Return[{expr}]];
permIndices=Permutations[{m1,m2,m3,m4}];
permSigns=Signature/@permIndices /. -1 ->sign;
Table[permSigns[[i]]*ReplacePart[aux,MapThread[Rule,{pos,permIndices[[i]]}]],{i,Length[permIndices]}]
]


Clear[shuffleIndicesEps]
shuffleIndicesEps[expr_]:=Module[{aux=expr,pos,permIndices,permSigns},
pos=Position[expr,_?(isM)];If[pos=={},Return[{expr}]];

permIndices=Permutations[mIndices];
permSigns=Signature/@permIndices /. -1 ->sign;

Table[permSigns[[i]]*ReplaceAll[aux,MapThread[Rule,{mIndices,permIndices[[i]]}]],{i,Length[permIndices]}]
]


Clear[ignoreM, reintroduceM]

ignoreM[expr_]:=expr/.{m1->m,m2->m,m3->m,m4->m}

reintroduceM[terms_] := Module[{M},
  M[0] = m1; M[1] = m2; M[2] = m3; M[3] = m4;  i=0;
  aux = terms // inactivePower;
  aux /. m :> M[Mod[i++,4]] // Activate
]
(*{A[m]B[j]J[m]H[j,m,m],(T[m]B[m]X[j,j])^2}//reintroduceM*)



Clear[generateAlternativeShapes]
generateAlternativeShapes[term_]:=Module[{aux=term},
aux=aux//rotationsOfTR;
aux=aux//Map[swapIndicesF]//Flatten//ignoreSigns;
aux=aux//Map[swapDummyIndices[j1,j2]]//Flatten;
aux=aux/.Times[_?Positive,rest__]:>Times[rest];

(*Here we also permute m indices, only possible for short lists*)
aux=aux//Map[shuffleIndicesEps]//Flatten;

aux=aux//ignoreSigns//DeleteDuplicates;
PrependTo[aux,term] (*Keep the original term in first possition*)
]


Clear[generateAlternativeShapesNoEpsSigned]
generateAlternativeShapesNoEpsSigned[term_]:=Module[{aux=term},
aux=aux//rotationsOfTR;
aux=aux//Map[swapIndicesF]//Flatten;
aux=aux//Map[swapDummyIndices[j1,j2]]//Flatten;
aux=aux/.Times[_?Positive,rest__]:>Times[rest];
aux=aux//.TR[a___,sign x_,b___]:>sign TR[a,x,b]//simplifySign;
PrependTo[aux,term] (*Keep the original term in first possition*)
]


(* ::Subsubsubsection::Closed:: *)
(*removeSymAntisymZeroes*)


Clear[removeSymAntisymZeroes]
removeSymAntisymZeroes[expr_]:=Module[{aux=expr},
aux=aux//Map[onTerms[removeSymAntisymJ]];
aux=aux//Map[onTerms[removeSymmtricalOnM]]]


(* ::Text:: *)
(*removeSymAntisymJ: symmetric[j1,j2]  f[j1,j2] = 0*)


(* ::Input:: *)
(*Clear[removeSymAntisymJ]*)
(**)
(*removeSymAntisymJ[0]:=0;*)
(*removeSymAntisymJ[expr_]:=If[isSymmetricOnJ[expr]&&!FreeQ[expr,DD[f:(fm|fp),_][___,j1,j2]],0,expr]*)


(* ::Input:: *)
(*(*TR[DD[fm,0][j1,j2],DD[u,0][m1]] TR[DD[u,0][j1],DD[u,0][j2]] TR[DD[u,0][m2],DD[u,0][m3],DD[u,0][m4]];*)
(*%//removeSymAntisymJ*)*)


(* ::Text:: *)
(*removeSymmtricalOnM: antisymmetric permutations of m-indices cannot leave invariant the term*)


(* ::Text:: *)
(*General protocol: swap index pairs or apply odd permutations to 4-tuples  [e.g. {m1,m2} -> {m2,m1} , {m1,m2,m3,m4} -> {m2,m3,m4,m1} ] and sort canonically the term. If it goes back to the original shape, it's symmetrical and antisymmetrical, i.e. it's 0*)


(* ::Input:: *)
(*Clear[isSymmetricalOnMPairs,isSymmetricalOn3MSwaps,removeSymmtricalOnM]*)
(*removeSymmtricalOnM[expr_]:=If[isSymmetricalOnMPairs[expr]||isSymmetricalOn3MSwaps[expr],0,expr]*)
(**)
(*isSymmetricalOnMPairs[0]:=True;*)
(*isSymmetricalOnMPairs[expr_?(#=!=0&)]:=Module[{input,mpairs,pair,res,answer},*)
(*input=expr//sortTracesBare;*)
(*mpairs=Subsets[{m1,m2,m3,m4},{2}];*)
(*answer=False;*)
(*Do[*)
(*pair=mpairs[[i]];*)
(*res1=input/.{pair[[1]]->pair[[2]],pair[[2]]->pair[[1]]}//sortTracesBare;*)
(*res2=input/.{pair[[1]]->pair[[2]],pair[[2]]->pair[[1]]}/.{j1->j2,j2->j1}//sortTracesBare;*)
(*If[res1-input===0||res2-input===0,answer=True;Break[],{}],*)
(*{i,Length[mpairs]}];*)
(*answer*)
(*]*)
(*(*TR[DD[u,0][j1]] TR[DD[fm,0][j1,m1],DD[u,0][m2]] TR[DD[u,0][m3],DD[u,0][m4]];*)*)
(*(*TR[DD[fm,0][j1,j1],DD[u,0][m1],DD[u,0][m2],DD[u,0][m3],DD[u,0][m4]];*)*)
(*(*%//isSymmetricalOnMPairs*)*)
(**)
(*(*Testing all odd permutations. There are 6 permutations with 3 swaps*)
(*https://mathworld.wolfram.com/OddPermutation.html*)*)
(*isSymmetricalOn3MSwaps[0]:=True;*)
(*isSymmetricalOn3MSwaps[expr_?(#=!=0&)]:=Module[{input,res,rule,answer,oddPerm3Swaps},*)
(*input=expr//sortTracesBare;*)
(*oddPerm3Swaps={{m2,m3,m4,m1},{m2,m4,m1,m3},{m3,m1,m4,m2},{m3,m4,m2,m1},{m4,m1,m2,m3},{m4,m3,m1,m2}};*)
(*answer=False;*)
(*Do[*)
(*rule=MapThread[Rule,{{m1,m2,m3,m4},oddPerm3Swaps[[i]]}];*)
(*res1=input/.rule//sortTracesBare;*)
(*res2=input/.rule/.{j1->j2,j2->j1}//sortTracesBare;*)
(*If[res1-input===0||res2-input===0,answer=True;Break[],{}],*)
(*{i,3}];*)
(*answer*)
(*]*)
(**)


(* ::Subsubsubsection::Closed:: *)
(*enhanceWithSimulatedEpsPermutations*)


Clear[getDictNoMToM]
getDictNoMToM[dictIn_List | dictIn_Dispatch] := Module[{dict,dictNoMToM},
(*Append a dictionary that transforms terms with plain (m) indices into terms with (m1,m2,m3,m4) indices. The resulting term exists in dictIn*)
dict=dictIn//Normal; (*Dispatch to List of Rules*)
dictNoMToM=dict/.Rule[lhs_,rhs_]:>Rule[lhs//ignoreM,lhs//ignoreSigns]//DeleteDuplicatesBy[First];
dictNoMToM
]

permIndices=Permutations[{m1,m2,m3,m4}];
permSigns=Signature/@permIndices /. -1 ->sign;
permRules = Table[MapThread[Rule,{{m1,m2,m3,m4},permIndices[[i]]}],{i,Length[permIndices]}];


Clear[simulateEpsPermutations]
simulateEpsPermutations[{dict_,dictNoMToM_}][term_]:=Module[{candidate,(*permIndices,permSigns,*)termPerm,stdTerm,  termsPerm},
candidate=(term//ignoreM)/.dictNoMToM;

i=0; termPerm=Null;
While[candidate=!=termPerm, 
termPerm=term/.permRules[[++i]];
If[i>Length[permIndices],Print["ERROR: candidate (", candidate,") and termPerm(", termPerm,") didn't match"];Abort[];]
];

stdTerm=permSigns[[i]]*(termPerm/.dict)
]

Clear[enhanceWithSimulatedEpsPermutations]
enhanceWithSimulatedEpsPermutations[dict_List | dict_Dispatch]:=Module[{dictDispatch,dictNoMToM},
(*Pre-calculate the dictionaries with Dispatch*)
dictNoMToM=dict//getDictNoMToM//Dispatch;
dictDispatch=dict//Dispatch;
Function[terms,terms//onTermsStrict[simulateEpsPermutations[{dictDispatch,dictNoMToM}]]//addSigns]
]


Clear[appendAuxDictOLD]
appendAuxDictOLD[dictIn_] := Module[{dict,dictNoMToM},
(*Append a dictionary that transforms terms with plain (m) indices into terms with (m1,m2,m3,m4) indices. The resulting term exists in dictIn*)
dict=dictIn//Normal; (*Dispatch to List of Rules*)
dictNoMToM=dict/.Rule[lhs_,rhs_]:>Rule[lhs//ignoreM,lhs//ignoreSigns]//DeleteDuplicatesBy[First]//Dispatch;
{dictIn,dictNoMToM}
]

Clear[enhanceWithSimulatedEpsPermutationsOLD]
enhanceWithSimulatedEpsPermutationsOLD[{dict_,dictNoMToM_}][terms_]:=Module[{},
terms//onTermsStrict[simulateEpsPermutations[{dict,dictNoMToM}]]//addSigns
]


(* ::Subsubsection::Closed:: *)
(*Trivial relations (standardizeShapes)*)


(* ::Text:: *)
(*This function standardizeShapes may not be necessary in other cases, where we can identify all the alternative shapes of the terms in one go, without the need to rewrite them in a standard way. See discussion in the main section of the calculation "Trivial relations"*)


Clear[standardizeShapes]
standardizeShapes[expr_]:=Module[{aux=expr},

aux=aux//Map[onTerms[assesJPair]];
aux=aux//orderJIndexfpfm//orderMJIndexfpfm;
aux=aux//sortTracesBare//addSigns//deleteDuplicatesSign;
aux=aux//sortTracesByField//Map[onTerms[reorderIndices]]//addSigns//deleteDuplicatesSign;
aux=aux//Map[onTerms[reorderFjj]]//addSigns//deleteDuplicatesSign;
aux=aux//Map[reOrderJSymCases]//addSigns//deleteDuplicatesSign
]

(*This is slower. Useful to debug sign-related problems*)
Clear[standardizeShapesKeepFloatingSign]
standardizeShapesKeepFloatingSign[expr_]:=Module[{aux=expr},

aux=aux//Map[onTerms[assesJPair]];
aux=aux//orderJIndexfpfm//orderMJIndexfpfm;
aux=aux//sortTracesBare;
aux=aux//Map[onTerms[reorderIndices]]//sortTracesByField//Map[onTerms[reorderIndices]];
aux=aux//Map[onTerms[reorderFjj]];
aux=aux//Map[reOrderJSymCases]
]


(* ::Subsubsubsection::Closed:: *)
(*orderFields: order arguments in traces consistently*)


(* ::Text:: *)
(*orderFields is the core function that defines the importance of each field in the new ordering. It accounts for derivatives, number of j indices, and position of j indices in sequential derivatives. But it is blind to which j index (j1 or j2) and which m index.*)


(* ::Input:: *)
(*Clear[orderFields]*)
(*orderFields[expr_?(Head@Head@#===DD&)]:=expr/.DD[f_,n_][ind___]:>(Switch[f,*)
(*chim,10+n,*)
(*chip,20+n,*)
(*fm, 30+n,*)
(*fp,40+n,*)
(*u,50+n]*)
(*-0.1*Length[Cases[{ind},_?isJ,99]]*)
(*-0.01*Total@Total[Position[{ind}[[1;;n]],_?isJ]])*)


(* ::Subsubsubsection::Closed:: *)
(*order(M)JIndexfpfm: reorder indices in fp/fm*)


(* ::Input:: *)
(*Clear[orderJIndexfpfm]*)
(*orderJIndexfpfm[expr_]:=expr/.DD[f:(fm|fp),n_][ind___,j2,j1]:>sign DD[f,n][ind,j1,j2]//pullSign*)
(*(*TR[DD[fm,4][m2,m4,m1,j2,j2,j1]];*)
(*TR[DD[fm,0][m1,j1],DD[fm,0][j2,j1],DD[fp,0][m2,j2],DD[u,1][m3,m4]]*)
(*%//orderJIndexfpfm*)*)


(* ::Input:: *)
(*Clear[orderMJIndexfpfm]*)
(*orderMJIndexfpfm[expr_]:=expr/.DD[f:(fp|fm),n_][ind___,m_?isM,j_?isJ]:>sign DD[f,n][ind,j,m]//pullSign*)
(*(*TR[DD[fm,4][m2,m4,m1,j2,m2,j2]];*)
(*TR[DD[fm,0][m1,j1],DD[fm,0][j2,j1],DD[fp,0][m2,j2],DD[u,1][m3,m4]]*)
(*%//orderMJIndexfpfm*)*)


(* ::Subsubsubsection::Closed:: *)
(*reorderFjj: reorder (j1,j2) antisymmetric pairs via f_j1j2 *)


(* ::Input:: *)
(*Clear[reorderFjj]*)
(*reorderFjj[0]:=0*)
(*reorderFjj[expr_?(#=!=0&)]:=Module[{aux=expr,pos},*)
(*aux=orderJIndexfpfm[aux];*)
(**)
(*aux=aux/.Times:>Inactive[Times]; (*needed bc changing jf can trigger a reordering*)*)
(*aux=aux/.Inactive[Times][args__]:>Inactive[Times]@@SortBy[{args},getTraceScore];*)
(*aux=aux/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);*)
(*auxFrozen=aux;*)
(**)
(**)
(*(*rename all j1,j2 and back*)*)
(*If[!FreeQ[aux,DD[f:(fm|fp),_][___,j1,j2]],aux=aux/.{j1->jf,j2->jf},{}];*)
(*aux=aux/.DD[f:(fm|fp),n_][ind___,jf,jf]:>DD[f,n][ind,j1,j2];*)
(**)
(*pos=Position[aux,jf];*)
(**)
(*If[pos==={},*)
(*Return[ aux//Activate],*)
(*aux=ReplacePart[aux,{pos[[1]]->j1,pos[[2]]->j2}];*)
(*(*If pos[[1]] had a j2 in auxFrozen, we are about to change the order: needs a sign*)*)
(*If[auxFrozen[[Sequence@@pos[[1]]]]===j2, sign aux//Activate, aux//Activate]*)
(*]*)
(*]*)
(**)
(*(*TR[DD[u,0][m1],DD[u,0][m2]] TR[DD[fm,0][j1,j2],DD[fm,0][j2,m3],DD[fm,0][j1,m4]];*)
(*TR[DD[fm,2][m1,m2,j1,j2],DD[fp,0][m3,m4],DD[fp,0][j1,j2]];*)
(*{%,%//reorderFjj}//see*)*)


(* ::Subsubsubsection::Closed:: *)
(*sortTracesByField: general for anomalous ChPT (U and small-u bases)*)


(* ::Text:: *)
(*sortTracesByField rotates the traces cyclically to find a standard ordering. There are a few special cases in which we have to break the ambiguity by hand*)


(* ::Input:: *)
(*Clear[cyclicSortByField,sortTracesByField]*)
(**)
(*sortTracesByField[expr_]:=expr/.TR[a__]:> cyclicSortByField[TR[a]];*)
(**)
(*cyclicSortByField[TR[args__]]:=Module[{aux={args},auxOrderScore,firstRot,extraRot},*)
(**)
(*(*First naive ordering*)*)
(*aux=RotateLeft[aux,Ordering[orderFields/@aux,1]-1];*)
(*auxOrderScore=orderFields/@aux;*)
(**)
(*(*Case Tr[A_j1,A_j2,A_j2] *)*)
(*If[CountDistinct[auxOrderScore]==1 , *)
(*If[Length[aux]==3&&!FreeQ[aux,_?isJ],*)
(*Switch[Count[aux,j1,99],*)
(*1,aux=RotateLeft[aux,Ordering[aux/.{m1->m,m2->m,m3->m,m4->m}/.{j1->A1,j2->A2},1]-1] ,*)
(*2, aux=RotateLeft[aux,Ordering[aux/.{m1->m,m2->m,m3->m,m4->m}/.{j1->A2,j2->A1},1]-1] ];*)
(*Return[TR@@aux]*)
(*,{}],*)
(*{}];*)
(**)
(*(*(*Case Tr[A_j1,A_j2,A_j2,A_j1] *)*)
(*(*NEW FOR U basis*)*)
(*(*first == last ?*)*)
(*If[CountDistinct[auxOrderScore]==1 , *)
(*If[Length[aux]==4&&!FreeQ[aux,_?isJ],*)
(*auxOrderScore=aux/.{m1->m,m2->m,m3->m,m4->m};*)
(*Do[*)
(*If[Order[auxOrderScore[[1]],auxOrderScore[[-1]]]==0,*)
(*aux=RotateRight[aux,1];*)
(*auxOrderScore=RotateRight[auxOrderScore,1],*)
(*Break],*)
(*{i,1,Length[aux]}];*)
(*,{}],*)
(*{}];*)
(**)
(*auxOrderScore=orderFields/@aux;*)*)
(**)
(**)
(*(*all fields are equal: return*)*)
(*If[CountDistinct[auxOrderScore]==1 , Return[TR@@aux],{}];*)
(**)
(*(*first == last ?*)*)
(*Do[*)
(*If[Order[auxOrderScore[[1]],auxOrderScore[[-1]]]==0,*)
(*aux=RotateRight[aux,1];*)
(*auxOrderScore=RotateRight[auxOrderScore,1],*)
(*Break],*)
(*{i,1,Length[aux]}];*)
(**)
(*(*Cases {a_,b__,a_,c__}*)*)
(*extraRot=0;*)
(* (*shortest list (b or c) goes first. If equal, look at elements*)*)
(*auxOrderScore/.{a_,b__,a_,c__}:>If[Order[{b},{c}]==-1,*)
(*(extraRot=Length[{a,b}];{a,b,a,c}),auxOrderScore];*)
(*aux=RotateLeft[aux,extraRot];*)
(*auxOrderScore=RotateLeft[auxOrderScore,extraRot];*)
(**)
(*(*Cases {x_,a__,x_,b__,x_,c__}*)*)
(*extraRot=0;*)
(* (*shortest list (a / b / c) goes first. If equal, look at elements*)*)
(*auxOrderScore/.{x_,a__,x_,b__,x_,c__}:>Which[*)
(*Order[{a},{b}]!=-1 && Order[{a},{c}]==+1 ,(extraRot=0;auxOrderScore),*)
(*Order[{b},{c}]!=-1 && Order[{b},{a}]==+1 ,(extraRot=Length[{x,a}];auxOrderScore),*)
(*Order[{c},{a}]!=-1&& Order[{c},{b}]==+1 ,(extraRot=Length[{x,a,x,b}];auxOrderScore)];*)
(*aux=RotateLeft[aux,extraRot];*)
(*auxOrderScore=RotateLeft[auxOrderScore,extraRot];*)
(**)
(*(*Cases {x1_,a_,x2_,a_,x2_,a_}*)*)
(*If[Length[aux]==6&&MatchQ[auxOrderScore,{x_,a_,x_,a_,x_,a_}],*)
(*Switch[Count[aux,j1,99],*)
(*1,aux=RotateLeft[aux,Ordering[aux/.{m1->m,m2->m,m3->m,m4->m}/.{j1->A1,j2->A2},1]-1] ,*)
(*2, aux=RotateLeft[aux,Ordering[aux/.{m1->m,m2->m,m3->m,m4->m}/.{j1->A2,j2->A1},1]-1] ];*)
(*Return[TR@@aux]*)
(*,{}];*)
(**)
(**)
(*TR@@aux]*)


(* ::Text:: *)
(*Examples:*)


(* ::Input:: *)
(*(*TR[DD[u,0][m2],DD[chip,0][m3],DD[u,0][m4],DD[u,0][j1]];*)
(*{%,%//sortTracesByField}//see*)
(*TR[DD[chim,2][j1,j2],DD[chim,2][m1,m2],DD[chim,2][j1,j2]];*)
(*{%,%//sortTracesByField}//see*)
(*TR[DD[u,0][m4],DD[u,0][j1]];*)
(*{%,%//sortTracesByField}//see*)*)


(* ::Text:: *)
(*Case of three js in a trace of identical elements*)


(* ::Input:: *)
(*(*target3j={TR[DD[u,0][j1],DD[u,0][m1]] TR[DD[u,1][m2,j1],DD[u,1][m3,j2],DD[u,1][m4,j2]],TR[DD[u,0][j1],DD[u,0][m1]] TR[DD[u,1][m2,j2],DD[u,1][m3,j1],DD[u,1][m4,j2]],TR[DD[u,0][j1],DD[u,0][m1]] TR[DD[u,1][m2,j2],DD[u,1][m3,j2],DD[u,1][m4,j1]]};*)
(*{%,%//Map[sortTracesByField]}//Transpose//see*)*)


(* ::Text:: *)
(*Case of Tr(\[Chi] Subscript[u, a] Subscript[f, bc])\[Epsilon]^(a b c)=-Tr(\[Chi] Subscript[u, a] Subscript[f, cb]) \[Epsilon]^(a b c)*)


(* ::Input:: *)
(*(*{TR[DD[u,0][m1],DD[fm,1][m2,m3,m4],DD[chim,0][]],TR[DD[chim,0][],DD[u,0][m1],DD[fm,1][m2,m4,m3]]};*)
(*{%,%//sortTracesByField//Map[reorderIndices,#]&//DeleteDuplicates}//readableNotation*)*)


(* ::Subsubsubsection::Closed:: *)
(*reOrderIndices : reorder m- and j-indices*)


(* ::Input:: *)
(*Clear[reorderIndices]*)
(*reorderIndices[0]:=0*)
(*reorderIndices[expr_?(#=!=0&)]:=Module[{posM,aux=expr,oddPerm1Swap,oddPerm3Swaps},*)
(*aux=aux/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);*)
(*aux=aux/.Times:>Inactive[Times];*)
(*aux=aux/.Inactive[Times][args__]:>Inactive[Times]@@SortBy[{args},getTraceScore];*)
(**)
(*(*j indices*) (*j before m! see codimd*)*)
(*posJ1=Position[aux,j1];*)
(*posJ2=Position[aux,j2];*)
(*If[posJ2 =!={}, *)
(*(*hasJ*)*)
(*If[Order[posJ1,posJ2]==-1,nposJ1=posJ2;nposJ2=posJ1,nposJ1=posJ1;nposJ2=posJ2];*)
(*aux=ReplacePart[aux,MapThread[Rule,{Join[nposJ1,nposJ2],Join[{j1,j1},{j2,j2}]}]]//Activate*)
(*,(*!hasJ*)*)
(*aux=aux//Activate*)
(*];*)
(**)
(*(*m indices*)*)
(*aux=aux/.Times:>Inactive[Times];*)
(*aux=aux/.Inactive[Times][args__]:>Inactive[Times]@@SortBy[{args},getTraceScore]; *)
(*auxFrozen=aux;*)
(**)
(*posM=Position[aux,_?isM];*)
(*aux=ReplacePart[aux,MapThread[Rule,{posM,{m1,m2,m3,m4}}]];*)
(**)
(**)
(*(*Check if the reordering gives a sign*)*)
(*oddPerm1Swap={{m2,m1,m3,m4},{m3,m2,m1,m4},{m4,m2,m3,m1},{m1,m3,m2,m4},{m1,m4,m3,m2},{m1,m2,m4,m3}};*)
(*oddPerm3Swaps={{m2,m3,m4,m1},{m2,m4,m1,m3},{m3,m1,m4,m2},{m3,m4,m2,m1},{m4,m1,m2,m3},{m4,m3,m1,m2}};*)
(*If[Extract[auxFrozen,posM]==={m1,m2,m3,m4}, Return[aux//Activate],{}];*)
(**)
(*If[MemberQ[Join[oddPerm1Swap,oddPerm3Swaps],Extract[auxFrozen,posM]],sign aux//Activate, aux//Activate]*)
(**)
(*]*)
(**)
(**)
(**)
(*(*{TR[DD[fm,0][j2,m4]]*TR[DD[u,0][j1],DD[u,0][j1]]TR[DD[u,0][j2],DD[u,0][m2]]*TR[DD[u,0][m1],DD[u,0][m3]]};*)
(*{TR[DD[chim,0][]] TR[DD[u,0][m1],DD[u,1][j1,j1]] TR[DD[u,0][m2],DD[u,1][m3,m4]],TR[DD[chim,0][]] TR[DD[u,0][m1],DD[u,1][m2,m3]] TR[DD[u,0][m4],DD[u,1][j1,j1]]};*)
(*{%,%//Map[reorderIndices]}//see*)*)
(**)
(**)
(*(*TR[DD[fm,0][m3,m4],DD[fp,0][m1,m2]] TR[DD[u,0][j1],DD[u,0][j2]]^2//assesJPair//sortTracesByField*)
(**)
(*{%,%//onTerms[reorderIndices]}//see*)*)


(* ::Input:: *)
(*Clear[assesJPair]*)
(*assesJPair[expr_]:=If[FreeQ[expr,j1],expr/.j2->j1,expr]*)
(**)
(* (*TR[DD[chim,1][m3]] TR[DD[fp,0][m1,m2],DD[fp,1][j2,j2,m4]]*)
(*{%,%//assesJPair}//see*)*)


(* ::Subsubsubsection::Closed:: *)
(*isPotentiallySymmetricOnJ: test symmetry of [j1,j2] making all m equal*)


(* ::Input:: *)
(*Clear[isPotentiallySymmetricOnJ,isSymmetricOnJ]*)
(*isPotentiallySymmetricOnJ[0]:=False;*)
(**)
(*isPotentiallySymmetricOnJ[expr_?(#=!=0&)]:=Module[{input=expr,inputSorted,mpairs,pair,res,answer,sub,posj,jswaps},*)
(**)
(*input=input/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);*)
(*input=input/.{m1->m,m2->m,m3->m,m4->m};*)
(*inputSorted = input//Activate//sortTracesBare;*)
(**)
(*posj=Join[Position[input,j1],Position[input,j2]];*)
(*jswaps={{j1,j2,j1,j2},{j1,j2,j2,j1}};*)
(*jswaps=Join[jswaps,jswaps/.{j1->j2,j2->j1}]//Reverse (*finds faster*);*)
(**)
(*If[Length[posj]!=4,Return[False],{}];*)
(**)
(*res=input;*)
(*answer=False;*)
(*Do[*)
(*sub[k] = ReplacePart[res,MapThread[Rule,{posj,jswaps[[k]]}]]//Activate//sortTracesBare;*)
(*If[sub[k]-inputSorted===0,answer=True;Break[],{}],*)
(*{k,4}];*)
(*answer*)
(*];*)
(**)
(*isSymmetricOnJ[expr_?(#=!=0&)]:=isPotentiallySymmetricOnJ[expr/.{m1->M1,m2->M2,m3->M3,m4->M4}]*)
(**)
(**)
(**)
(*(*Very slow. Not needed for small-u basis. But more general than isPotentiallySymmetric. Used in contact terms (EF)*)*)
(*Clear[isSymmetricOnJWithMPermutations]*)
(**)
(*isSymmetricOnJWithMPermutations[expr_?(#=!=0&)]:=Module[{input=expr,inputSorted,mpairs,pair,res,answer,sub,posj,jswaps,mEvenPermutations,replaceSymM},*)
(**)
(*input=input/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);*)
(*input=input/.Times:>Inactive[Times];*)
(*inputSorted = input//Activate//sortTracesBare;*)
(**)
(*posj=Join[Position[input,j1],Position[input,j2]];*)
(*jswaps={{j1,j2,j1,j2},{j1,j2,j2,j1}};*)
(*jswaps=Join[jswaps,jswaps/.{j1->j2,j2->j1}]//Reverse (*finds faster*);*)
(**)
(*mEvenPermutations=Select[Permutations[{m1,m2,m3,m4}],Signature[#]==+1&];*)
(*replaceSymM=Table[MapThread[Rule,{{m1,m2,m3,m4},mEvenPermutations[[i]]}],{i,Length[mEvenPermutations]}];*)
(**)
(*If[Length[posj]!=4,Return[False],{}];*)
(**)
(*answer=False;*)
(**)
(*Do[*)
(*res=input/.replaceSymM[[l]];*)
(*Do[*)
(*sub[k] = ReplacePart[res,MapThread[Rule,{posj,jswaps[[k]]}]]//Activate//sortTracesBare;*)
(*If[sub[k]-inputSorted===0,answer=True;Break[],{}]*)
(*,{k,4}];*)
(*If[answer,Break[],{}]*)
(*,{l,Length[mEvenPermutations]}];*)
(*answer*)
(*];*)


(* ::Subsubsubsection::Closed:: *)
(*reOrderJSymCases: reorder (j1, j2) (anti)symmetric pairs (via m pair exchanges)*)


(* ::Input:: *)
(*Clear[reOrderJSymCases]*)
(**)
(*reOrderJSymCases[0]:=0;*)
(*reOrderJSymCases[expr_?(#=!=0&)]:=Module[{input=expr,inputSorted,mpairs,pair,res,answer,sub,posj,jswaps,kstop,istop,posSPair1,posSPair2,unOrdered=False},*)
(*input=input/.Power[a_,b_?Positive]:>(Inactive[Times]@@ConstantArray[a,b]);*)
(*inputSorted = input//Activate//sortTracesBare;*)
(**)
(*posj=Join[Position[input,j1],Position[input,j2]];*)
(*jswaps={{j1,j2,j1,j2},{j1,j2,j2,j1}};*)
(*jswaps=Join[jswaps,jswaps/.{j1->j2,j2->j1}]//Reverse (*finds faster*);*)
(*mpairs=Subsets[{m1,m2,m3,m4},{2}];*)
(*mpairs=Join[{{m1,m1}},mpairs];*)
(**)
(*(*Triage of terms: has 4 j indices and isPotentiallySymmetricOnJ*)*)
(*If[Length[posj]!=4,Return[expr],{}];*)
(*If[Order@@posj[[{2,3}]]==1,Return[expr],{}];(*already ordered! ={j1,j1,j2,j2}*)*)
(*If[isPotentiallySymmetricOnJ[expr],{},Return[expr]];*)
(**)
(*(*test symmetry doing all substitutions of m and j indices*)*)
(*answer=False;*)
(*Do[*)
(*pair=mpairs[[i]];*)
(*res=input/.{pair[[1]]->pair[[2]],pair[[2]]->pair[[1]]};*)
(*Do[*)
(*sub[k] = ReplacePart[res,MapThread[Rule,{posj,jswaps[[k]]}]]//Activate//sortTracesBare;*)
(*If[sub[k]-inputSorted===0,answer=True;kstop=k;Break[],{}],*)
(*{k,4}];*)
(*If[answer,istop=i;Break[],{}],*)
(*{i,Length[mpairs]}];*)
(**)
(*If[answer,{},Return[expr]];*)
(**)
(*(*find symmetric [j1,j2] pairs*)*)
(*Switch[kstop,*)
(*1|3,(posSPair1=posj[[{1,3}]];posSPair2=posj[[{2,4}]]),*)
(*2|4,(posSPair1=posj[[{1,4}]];posSPair2=posj[[{2,3}]])];*)
(**)
(*res=input;*)
(**)
(*(*Assess order of symmetric [j1,j2] pairs]*)*)
(*If[Order@@posSPair1==-1,unOrdered=!unOrdered;*)
(*res=ReplacePart[res,MapThread[Rule,{posSPair1,{j2,j1}}]],*)
(*{}];*)
(*If[Order@@posSPair2==-1, unOrdered=!unOrdered;*)
(*res=ReplacePart[res,MapThread[Rule,{posSPair2,{j2,j1}}]],*)
(*{}];*)
(**)
(*(*(If istop={2...7} the symmetry is due to the exchange of [mpairs] and there's a sign)*)*)
(*If[unOrdered&&MemberQ[{2,3,4,5,6,7},istop],sign res//Activate, res//Activate]*)
(**)
(*]*)
(**)
(*(*TR[DD[u,0][j1],DD[u,0][j2]] TR[DD[fm,0][j2,m1],DD[fm,0][j1,m2],DD[fm,0][m3,m4]];*)
(*{%,%//reOrderJSymCases}//see*)
(*TR[DD[fp,0][j1,m1],DD[fp,0][j2,m2]] TR[DD[u,0][j2],DD[u,1][j1,m3],DD[u,0][m4]];*)
(*{%,%//reOrderJSymCases}//see*)*)
(**)
(*(*{TR[DD[u,0][j1],DD[u,0][j2]] TR[DD[fm,0][j2,m1],DD[fm,0][j1,m2],DD[fm,0][m3,m4]],TR[DD[fp,0][j1,m1],DD[fp,0][j2,m2]] TR[DD[u,0][j2],DD[u,1][j1,m3],DD[u,0][m4]]};*)
(*{%,%//Map[reOrderJSymCases]}//see*)*)
(**)
(**)
(*(*TR[DD[fp,1][j2,j1,m1],DD[u,0][m2]] TR[DD[u,1][m3,j1],DD[u,1][m4,j2]];*)
(*{%,%//reOrderJSymCases}//see*)*)
(**)


(* ::Subsubsubsection::Closed:: *)
(*Wrapper: orderCanonically [OLD]*)


(* ::Input:: *)
(*Clear[orderCanonicallyAndDeleteDuplicates]*)
(*orderCanonicallyAndDeleteDuplicates[expr_]:=Module[{aux=expr},*)
(**)
(*aux=aux//Map[onTerms[assesJPair]];*)
(*aux=aux//orderJIndexfpfm//orderMJIndexfpfm;*)
(*aux=aux//sortTracesBare//addSigns//deleteDuplicatesSign;*)
(*aux=aux//sortTracesByField//Map[onTerms[reorderIndices]]//addSigns//deleteDuplicatesSign;*)
(*aux=aux//Map[onTerms[reorderFjj]]//addSigns//deleteDuplicatesSign*)
(*]*)


(* ::Input:: *)
(*Clear[orderCanonically]*)
(*orderCanonically[expr_]:=Module[{aux=expr},*)
(**)
(*aux=aux//Map[onTerms[assesJPair]];*)
(*aux=aux//orderJIndexfpfm//orderMJIndexfpfm;*)
(*aux=aux//sortTracesBare;*)
(*aux=aux//Map[onTerms[reorderIndices]]//sortTracesByField//Map[onTerms[reorderIndices]];*)
(*aux=aux//Map[onTerms[reorderFjj]]*)
(*]*)


(* ::Subsubsection::Closed:: *)
(*Operators relations*)


(* ::Subsubsubsection::Closed:: *)
(*[TD] Total derivatives - substitute indices*)


Clear[subsInd4,subsInd6,subsInd8]
subsInd4=Inner[ReverseApplied[Rule],indPerm4,{x,a,b,c},List];
subsInd6=Inner[ReverseApplied[Rule],indPerm6,{x,a,b,c,d,e},List];
subsInd8=Inner[ReverseApplied[Rule],indPerm8,{x,a,b,c,d,e,f,g},List];


Clear[subsIndices]
subsIndices[expr_,indPerm4_,indPerm6_,indPerm8_]:=Module[{nIndices},
nIndices=Which[!FreeQ[expr,g],8,!FreeQ[expr,e],6,!FreeQ[expr,c],4];
Switch[nIndices,
4,expr/.subsInd4,
6,expr/.subsInd6,
8,expr/.subsInd8
]
]


(* ::Subsubsection::Closed:: *)
(*Translate basis*)


Clear[additionalOpesFor]
additionalOpesFor[terms_List][relationMatrix_] := 
ope/@Range[Last[Dimensions[relationMatrix]]+1 , Last[Dimensions[relationMatrix]] + Length[terms]]



Clear[toSmallUBasis]
toSmallUBasis[terms_]:=Module[
{f1,f2, SEQ, COM, ACOM,Du, subsChit, changeNotationDer, derToSmallU,chiralOfX, 
subFieldsWithoutDer, cleanTracesFull,aux,},

SEQ[A___,Plus[a_,b_],B___]:=SEQ[A,a,B]+SEQ[A,b,B];
SEQ[A___,a_*com[b__],B___]:=a*SEQ[A,com[b],B];
SEQ[A___,a_*acom[b__],B___]:=a*SEQ[A,acom[b],B];
SEQ[A___,a_*SEQ[b__],B___]:=a*SEQ[A,SEQ[b],B];
SEQ[A___,a_*Du[b_][c__],B___]:=a*SEQ[A,Du[b][c],B];

COM[A_,B_]:=SEQ[A,B]-SEQ[B,A];
ACOM[A_,B_]:=SEQ[A,B]+SEQ[B,A];

Du[i_][A___,a_ SEQ[b__],B___]:=a*Du[i][A,SEQ[b],B];
Du[i_][A___,a_+b_, B___]:=Du[i][A,a,B] + Du[i][A,b,B];
(*Du[i_][DD[f1_,0][i1___],DD[f2_,0][i2___]]:=SEQ[Du[i][DD[f1,0][i1]],DD[f2,0][i2]]+SEQ[DD[f1,0][i1],Du[i][DD[f2,0][i2]]]*)
Du[i_][a:DD[__][___],b__?(Head[Head[#]]===DD&)]:= SEQ[Du[i][a],b] + SEQ[a,Du[i][b]];
(*Du[i_][a:DD[__][___],b__?(Head[#]===seq&)]:= SEQ[Du[i][a],b] + SEQ[a,Du[i][b]];*)
Du[i_][a:DD[__][___],b:DD[__][___]]:=SEQ[Du[i][a],b] + SEQ[a,Du[i][b]];
Du[i_][a:DD[__][___],b:DD[__][___]]:=SEQ[Du[i][a],b] + SEQ[a,Du[i][b]];
Du[i_][SEQ[b__]]:=Du[i][b];
Du[i_][A___,- a_ ,B___]:=-Du[i][A,a,B];

subsChit =(#/.TR[A___,f1[chit],B___]:>TR[B,A,f2[chit]]/.
TR[A___,f1[chit]]:>TR[u,A,u]TR[u,f2[chid],u]-TR[u,A,u,u,f2[chid],u]/.
TR[A___,f1[chitd],B___]:>TR[B,A,f2[chitd]]/.
TR[A___,f1[chitd]]:>TR[ud,A,ud]TR[ud,f2[chi],ud]-TR[ud,A,ud,ud,f2[chi],ud]&)/. 
f1[a_] -> DD[a,0][ind___] /. f2[a_]->DD[a,0][ind];

changeNotationDer=DD[f_,n_?(#>0&)][i1_,ind___]:>dU[i1][DD[f,n-1][ind]];

derToSmallU=dU[i_][X_]:>(
chiralOfX={First@#,Last@#}&@Cases[X,u|ud,99,Heads->True];
(*Print[X, " :  ", chiralOfX];*)
Switch[chiralOfX, (*Notice the not at all confusing notation: u, ud, du, dU, Du and DD[u]*)
{u,u},   seq[u, (du[i][ud,X,ud]  - (I/2) acom[DD[u,0][i],seq[ud,X,ud]]), u],
{ud,ud}, seq[ud, (du[i][u,X,u]   + (I/2) acom[DD[u,0][i],seq[u,X,u]]), ud],
{u,ud},  seq[u, (du[i][ud,X,u]   - (I/2) com[DD[u,0][i],seq[ud,X,u]]), ud],
{ud,u},  seq[ud, (du[i][u,X,ud]  + (I/2) com[DD[u,0][i],seq[u,X,ud]]), u]
]);


subFieldsWithoutDer={
f1[chi]:>(1/2)seq[u,f2[chip] + f2[chim],u],
f1[chid]:>(1/2)seq[ud,f2[chip] - f2[chim],ud],
f1[FL]:>  (1/2)seq[ud,f2[fp] + f2[fm],u],
f1[FR]:>  (1/2)seq[u,f2[fp] - f2[fm],ud]
};
subFieldsWithoutDer = subFieldsWithoutDer /.f1[a_] -> DD[a,0][ind___] /. f2[a_]->DD[a,0][ind];

cleanTracesFull[expr_]:=FixedPoint[(#/.SEQ->seq//cleanTraces)/.seq->Sequence&,expr];

aux=terms;
aux=aux//subsChit;
aux=aux//.changeNotationDer/.subFieldsWithoutDer;
aux=aux//.derToSmallU;
aux=aux/.seq->SEQ/.du->Du/.com->COM/.acom->ACOM//ExpandAll;
aux=aux//cleanTracesFull;
aux=aux//.Du[ii_][A___,ud,u,B___]-> Du[ii][A,B] //. Du[ii_][A___,u,ud,B___]->Du[ii][A,B] /. SEQ->seq//cleanTraces;
aux=aux/.TR[A__]:>RotateLeft[TR[A]] //. TR[A___,ud,u,B___]->TR[A,B] //.TR[A___,u,ud,B___]->TR[A,B];
aux=aux/.TR[A__]:>RotateLeft[TR[A]] //. TR[A___,ud,u,B___]->TR[A,B] //.TR[A___,u,ud,B___]->TR[A,B]//ExpandAll;
aux=aux//.Du[ii_][-a]:>- DD[ii][a_];
aux=aux//.Du[ii_][DD[f_,n_][ind0___]]:>DD[f,n+1][ii,ind0]//cleanTracesFull;
aux=aux//.Du[ii_][DD[f_,n_][ind0___]]:>DD[f,n+1][ii,ind0]//cleanTracesFull;


If[Count[aux,u|ud]>0, Print["ERROR: Transformed terms are not chiral invariant. They contain u or ud."]];

aux
]


(* ::Subsection::Closed:: *)
(*Options*)


ORDER=8;
zeroTrF=True;


(* ::Subsection::Closed:: *)
(*Construct possible terms*)


(* ::Text:: *)
(*Keep p^n terms. 4, 6, or 8 indices. Odd intrinsic parity.*)
(*Introduce derivatives.*)
(*Introduce traces.*)
(*Introduce indices.*)


getCombinationsWithSymmetries[ORDER,{4,6,8},OddQ]//showLength;
%//Map[applyDerivativesAndPermutations]//showLengthFlat;
%//introduceTraces//showLengthFlat;
%//insertIndexPlaceHolders//Map[insertIndices]//showTiming;
possibleTerms=%//Flatten//showLength;


(* ::Subsection::Closed:: *)
(*Trivial relations*)


(* ::Text:: *)
(*(time 7')*)


(* ::Subsubsection::Closed:: *)
(*Get the initial basis*)


(* ::Text:: *)
(*Reduce the list of possibleTerms accounting for obvious zeroes, permutations of indices and cyclicity of traces. We do this in two alternative ways*)
(**)
(*1. Simpler method: (1) remove easy zeroes following from definitions;  (2) ignore Levi-Civita 'm'  index permutations (can only give signs), generate all possible shapes of each term, sort them, save first shape of each term, delete duplicates, reintroduce epsilon indices; (3) (use a more involved function to) remove terms that are both symmetric and antisymmetric on some index permutation. This leads to 402 (31568) different possible terms in p^6 (p^8)*)


possibleTerms//removeEasyZeroes//DeleteCases[0]//showLength;
lagWithZeroes=%//ignoreM//Map[generateAlternativeShapesNoEps]//Map[Sort]//Map[First]//DeleteDuplicates//reintroduceM//showTiming//showLength;
lag=%//removeSymAntisymZeroes//DeleteCases[0]//showTiming//showLength;


(* ::Text:: *)
(*2. More involved method: in step (2), rewrite each term into a standard shape, but not by generating all shapes first and comparing, but by defining a canonical order for relative position of indices, fields inside traces, relative position of two traces, etc. Defining this standard way of writing the terms is no easy task and one has to break all possible ambiguities by hand (symmetry of indices, repeated elements in traces, ...). We kept this method here for comparison. It is also slightly faster, even accounting for Levi-Civita indices.*)


possibleTerms//removeEasyZeroes//DeleteCases[0]//showLength;
lagWithZeroes2=%//standardizeShapes//showTiming//showLength;
lag2=%//removeSymAntisymZeroes//DeleteCases[0]//showTiming//showLength;


(* ::Subsubsection::Closed:: *)
(*Alternative shapes of terms*)


(* ::Text:: *)
(*Functions to 'reshape' the terms fast using dictionaries (replacement rules). First generate all* ways of writing the terms (shapes) *)
(**)
(** Zero terms (~1k terms). *)
(** All terms (~31k terms). Not possible, it would eat the RAM. Levi-Civita indices are ignored (NoEps)*)


lagShapesZeroes = Complement[lagWithZeroes,lag]//Map[generateAlternativeShapes]//showTiming//showLengthFlat;
lagShapes=lag//Map[generateAlternativeShapesNoEpsSigned]//showTiming//showLengthFlat;


(* ::Subsubsection::Closed:: *)
(*Reshape terms [import]*)


(* ::Text:: *)
(*[The [import] tag indicates the (3) cells that must be executed if importing previous data. These cells are also part of the normal calculation flow]*)


(*import["P8"]*)


(* ::Text:: *)
(*The different shapes are mapped onto the first one, and the rules converted into replacement functions. Then the wrappers "reshapeTerms" are defined, which are used in the rest of the calculation.*)


removeSymAntisymZeroesDict = lagShapesZeroes//Map[getDictionaryOfShapes]//landRulesOnZero//Flatten//rulesToFunction//showTiming;
standardizeShapesDict = lagShapes//Map[getDictionaryOfShapes]//Flatten//enhanceWithSimulatedEpsPermutations//showTiming;

Clear[reshapeTerms,reshapeTermsBare]
reshapeTerms[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//DeleteCases[0]//deleteDuplicatesSign;
reshapeTermsBare[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//DeleteCases[0];


(* ::Subsubsection::Closed:: *)
(*Identify terms [import]*)


(* ::Text:: *)
(*Function to transform term expressions into labels ope[i], where i is the position of the term in 'lag'. Only works after reshapeTerms has been applied.*)


lagDictionary=PositionIndex[lag];
lagScores=lag//Map[termScore];

Clear[identifyTerms]
identifyTerms = makeIdentifyTerms[lag,lagDictionary,lagScores];


(* ::Text:: *)
(*The inverse function can be useful to inspect the final relations. It is used in the last part of the example, "Reduce to minimal basis"*)


Clear[rawOpesToTerms]
rawOpesToTerms[expr_]:=expr/.ope[i_]:>lag[[i]]


lag//identifyTerms//showTiming;
(%/.ope[n_]:>n//Total) == (Range[Length[lag]]//Total)


(*Export[NotebookDirectory[]<>"/save/test.m",
{FullDefinition[identifyTerms],lag,possibleTerms,FullDefinition[reshapeTerms]
}];*)


(* ::Subsection::Closed:: *)
(*Operator relations*)


(* ::Text:: *)
(*(time 45')*)


(* ::Subsubsection::Closed:: *)
(*[TD] Total derivatives*)


(* ::Text:: *)
(*Generate anew all terms with 3/5/7 indices (called a,b,c,...) with odd intrinsic parity at O(p7/p5) *)


getCombinationsWithSymmetries[ORDER-1,{3,5,7},OddQ];
%//Map[applyDerivativesAndPermutations]//introduceTraces;
%//insertIndexPlaceHolders//Flatten//showLength;
termsp7=%//Map[insertOneIndexCombination[#,{a,b,c,d,e,f,g}]&];


(* ::Text:: *)
(*Take the total derivative of each term, adding the 8th/6th/4th index (called x), and distribute the derivative over the product.*)
(*Then replace indices by the usual names (m1, m2. m3, m4, j1, j2). Relations are obtained as linear combinations of ope[i] that are equal to zero.*)


termsp7//Map[Dx];
fullTD=%//Map[subsIndices[#,subsInd4,subsInd6,subsInd8]&]//Flatten//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. Store relations in relTD.*)


fullTD//reshapeTerms//showTiming//showLength;
relTD=%//identifyTerms//DeleteDuplicates//showLength;


(* ::Subsubsection::Closed:: *)
(*[FMU] Relation of fm and Du*)


(* ::Text:: *)
(*Define the identities*)


ruleFMU1=tagX[u,n_?(#==1&)][ind___,a_,b_]:>DD[u,n][ind,a,b] - DD[u,n][ind,b,a]+DD[fm,n-1][ind,a,b];
tagFMU1[tag_]:=DD[u,n_?(#==1&)][ind___,a_,b_]:>tag[u,n][ind,a,b] /;i++<1;

ruleFMU2=tagX[fm,n_?(#==0&)][ind___,a_,b_]:>DD[u,n+1][ind,a,b] - DD[u,n+1][ind,b,a]+DD[fm,n][ind,a,b];
tagFMU2[tag_]:=DD[fm,n_?(#==0&)][ind___,a_,b_]:>tag[fm,n][ind,a,b] /;i++<1;

checkRule[tagFMU1,ruleFMU1];
checkRule[tagFMU2,ruleFMU2];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules and get the operator relations*)


lagFMU1=lag//findWithMinNDer[u,1]//showLength;
lagFMU2=lag//findWithMinNDer[fm,0]//showLength;

fullFMU1=getRelationsFromRule[lagFMU1,ruleFMU1,tagFMU1,DD]//showTiming;
fullFMU2=getRelationsFromRule[lagFMU2,ruleFMU2,tagFMU2,DD]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullFMU1,fullFMU2]//reshapeTerms//showTiming;
relFMU=%//identifyTerms//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[EOM] Equations of motion*)


(* ::Text:: *)
(*Define the identities*)


ruleEOM1=tagX[u,n_?(#==1&)][ind___,a_,a_]:>DD[u,n][ind,a,a] -(1/2)ii DD[chim,n-1][ind]+TR[(1/2)(1/Nf)ii DD[chim,n-1][ind]];
tagEOM1[tag_]:=DD[u,n_?(#==1&)][ind___,a_,a_]:>tag[u,n][ind,a,a] /;i++<1;

ruleEOM2=tagX[chim,n_?(#==0&)][ind___]:>DD[u,n+1][ind,j2,j2] -(1/2)ii DD[chim,n][ind]+TR[(1/2)(1/Nf)ii DD[chim,n][ind]];
tagEOM2[tag_]:=DD[chim,n_?(#==0&)][ind___]:>tag[chim,n][ind] /;i++<1;

checkRule[tagEOM1,ruleEOM1];
checkRule[tagEOM2,ruleEOM2];


(* ::Text:: *)
(*Get the operator relations*)


fullEOM1=getRelationsFromRule[lag,ruleEOM1,tagEOM1,DD]//onTermsStrict[assesJPair]//showTiming;
fullEOM2=getRelationsFromRule[lag,ruleEOM2,tagEOM2,DD]//onTermsStrict[assesJPair]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullEOM1,fullEOM2]//reshapeTerms//showTiming;
relEOM=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[BI] Bianchi identities*)


(* ::Subsubsubsection::Closed:: *)
(*BIm : introduced through fm*)


(* ::Text:: *)
(*Define the identities*)


ruleBIm1=tagX[fm,1][a_,b_,c_]:>DD[fm,1][a,b,c] +DD[fm,1][b,c,a]+DD[fm,1][c,a,b]+
(ii/2)(seq[DD[u,0][a] ,DD[fp,0][b,c]] + 
seq[DD[u,0][b] ,DD[fp,0][c,a]] +
seq[DD[u,0][c] ,DD[fp,0][a,b]])-
(ii/2)(seq[DD[fp,0][b,c],DD[u,0][a] ] +
 seq[DD[fp,0][c,a],DD[u,0][b] ] +
seq[DD[fp,0][a,b],DD[u,0][c]]);

Clear[a,b,c,A,B]

ruleBIm2a=tagX[A___,DD[u,0][a_],DD[fp,0][b_,c_],B___]->TR[A,ruleBIm1[[2]],B];
ruleBIm2b=tagX[DD[fp,0][b_,c_],A__,DD[u,0][a_]]->TR[ruleBIm1[[2]],A];

ruleBIm3a=tagX[A___,DD[fp,0][b_,c_],DD[u,0][a_],B___]->TR[A,ruleBIm1[[2]],B];
ruleBIm3b=tagX[DD[u,0][a_],A__,DD[fp,0][b_,c_]]->TR[ruleBIm1[[2]],A];

tagBIm1[tag_]:=DD[fm,1][a_,b_,c_]:>tag[fm,1][a,b,c] /;i++<1;
tagBIm2a[tag_]:=TR[A___,DD[u,0][a_],DD[fp,0][b_,c_],B___]:>tag[A,DD[u,0][a],DD[fp,0][b,c],B]/;i++<1;
tagBIm2b[tag_]:=TR[DD[fp,0][b_,c_],A__,DD[u,0][a_]]:>tag[DD[fp,0][b,c],A,DD[u,0][a]]/;i++<1;
tagBIm3a[tag_]:=TR[A___,DD[fp,0][b_,c_],DD[u,0][a_],B___]:>tag[A,DD[fp,0][b,c],DD[u,0][a],B]/;i++<1;
tagBIm3b[tag_]:=TR[DD[u,0][a_],A__,DD[fp,0][b_,c_]]:>tag[DD[u,0][a],A,DD[fp,0][b,c]]/;i++<1;

checkRule[tagBIm1,ruleBIm1];
checkRule[tagBIm2a,ruleBIm2a];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules*)


lagBI1=Select[lag,Count[#,DD[(fm|fp),n_?(#>0&)][ind___],99]>0&]//showLength;
lagBI2=Select[lag,Count[#,TR[___,DD[u,0][__],DD[(fm|fp),0][__],___]|TR[DD[(fm|fp),0][__],___,DD[u,0][__]],99]>0&]//showLength;
lagBI3=Select[lag,Count[#,TR[___,DD[(fm|fp),0][__],DD[u,0][__],___]|TR[DD[u,0][__],___,DD[(fm|fp),0][__]],99]>0&]//showLength;


(* ::Text:: *)
(*Get the operator relations*)


fullBIm1=getRelationsFromRule[lagBI1,ruleBIm1,tagBIm1,DD]//showTiming;
fullBIm2a=getRelationsFromRule[lagBI2,ruleBIm2a,tagBIm2a,TR]//showTiming;
fullBIm2b=getRelationsFromRule[lagBI2,ruleBIm2b,tagBIm2b,TR]//showTiming;
fullBIm3a=getRelationsFromRule[lagBI3,ruleBIm3a,tagBIm3a,TR]//showTiming;
fullBIm3b=getRelationsFromRule[lagBI3,ruleBIm3b,tagBIm3b,TR]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullBIm1,fullBIm2a,fullBIm2b,fullBIm3a,fullBIm3b]//reshapeTerms//showTiming;
relBIm=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsubsection::Closed:: *)
(*BIp : introduced through fp*)


(* ::Text:: *)
(*Define the identities*)


ruleBIp1=ruleBIm1/.{fp->fm,fm->fp};
ruleBIp2a=ruleBIm2a/.{fp->fm,fm->fp};
ruleBIp2b=ruleBIm2b/.{fp->fm,fm->fp};
ruleBIp3a=ruleBIm3a/.{fp->fm,fm->fp};
ruleBIp3b=ruleBIm3b/.{fp->fm,fm->fp};


Clear[tagBIp1,tagBIp2a,tagBIp2b,tagBIp3a,tagBIp3b]
tagBIp1[expr_]=tagBIm1[expr]/.{fp->fm,fm->fp};
tagBIp2a[expr_]=tagBIm2a[expr]/.{fp->fm,fm->fp};
tagBIp2b[expr_]=tagBIm2b[expr]/.{fp->fm,fm->fp};
tagBIp3a[expr_]=tagBIm3a[expr]/.{fp->fm,fm->fp};
tagBIp3b[expr_]=tagBIm3b[expr]/.{fp->fm,fm->fp};

checkRule[tagBIp1,ruleBIp1];
checkRule[tagBIp2a,ruleBIp2a];


(* ::Text:: *)
(*Get the operator relations*)


fullBIp1=getRelationsFromRule[lagBI1,ruleBIp1,tagBIp1,DD]//showTiming;
fullBIp2a=getRelationsFromRule[lagBI2,ruleBIp2a,tagBIp2a,TR]//showTiming;
fullBIp2b=getRelationsFromRule[lagBI2,ruleBIp2b,tagBIp2b,TR]//showTiming;
fullBIp3a=getRelationsFromRule[lagBI3,ruleBIp3a,tagBIp3a,TR]//showTiming;
fullBIp3b=getRelationsFromRule[lagBI3,ruleBIp3b,tagBIp3b,TR]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullBIp1,fullBIp2a,fullBIp2b,fullBIp3a,fullBIp3b]//reshapeTerms//showTiming;
relBIp=%//identifyTerms//deleteDuplicatesSign//showLength;


relBI=Join[relBIm,relBIp]//showLength;


(* ::Subsubsection::Closed:: *)
(*[SCH] Schouten identity*)


(* ::Text:: *)
(*Preselect terms of the basis and get relations*)


lagSCH=Select[lag,Count[#,j1 ,99]>0&]//showLength;
fullSCH=lagSCH//Map[getRelationSCH4m]//Flatten//DeleteDuplicates//showTiming//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


(* ::Text:: *)
(*Takes 2' *)


fullSCH//reshapeTerms//showTiming;
relSCH=%//identifyTerms//deleteDuplicatesSign//showLength;


relSCH//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[COM] Commutation of derivatives*)


(* ::Text:: *)
(*Define the identities*)


Clear[a,b,c,A,B]

ruleCOM1=tagX[X_,n_?(#>=2&)][a_,b_,ind___]:>
-DD[X,n][a,b,ind] +DD[X,n][b,a,ind]  +
(1/4)*(
seq[DD[u,0][a],DD[u,0][b],DD[X,n-2][ind]] -
 seq[DD[u,0][b],DD[u,0][a],DD[X,n-2][ind]]) -( ii/2) seq[DD[fp,0][a,b],DD[X,n-2][ind]]- 
(1/4)*(
seq[DD[X,n-2][ind],DD[u,0][a],DD[u,0][b]] - 
seq[DD[X,n-2][ind],DD[u,0][b],DD[u,0][a]]) + ( ii/2) seq[DD[X,n-2][ind],DD[fp,0][a,b]];

tagCOM1[tag_]:=DD[X_,n_?(#>=2&)][ind___]:>tag[X,n][ind] /;i++<1;

ruleCOM2a=tagX[DD[u,0][a_],DD[u,0][b_],DD[X_,n_][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM2a[tag_]:=TR[DD[u,0][a_],DD[u,0][b_],DD[X_,n_][ind___],A___]:>tag[DD[u,0][a],DD[u,0][b],DD[X,n][ind],A]/;i++<1;

ruleCOM3a=tagX[DD[fp,0][a_,b_],DD[X_,n_][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM3a[tag_]:=TR[DD[fp,0][a_,b_],DD[X_,n_][ind___],A___]:>tag[DD[fp,0][a,b],DD[X,n][ind],A]/;i++<1;

(*Not necesary 2b and 3b: 9331 rel anyway*)
ruleCOM2b=tagX[DD[X_,n_][ind___],DD[u,0][a_],DD[u,0][b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM2b[tag_]:=TR[DD[X_,n_][ind___],DD[u,0][a_],DD[u,0][b_],A___]:>tag[DD[X,n][ind],DD[u,0][a],DD[u,0][b],A]/;i++<1;

ruleCOM3b=tagX[DD[X_,n_][ind___],DD[fp,0][a_,b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM3b[tag_]:=TR[DD[X_,n_][ind___],DD[fp,0][a_,b_],A___]:>tag[DD[X,n][ind],DD[fp,0][a,b],A]/;i++<1;

checkRule[tagCOM1,ruleCOM1];
(*In this case the other rules are a bit too general to be checked*)


(* ::Text:: *)
(*Preselect terms*)


lagCOM1=Select[lag,Count[#,DD[_,n_?(#>=2&)][ind__],99]>= 1&]//showLength;
lagCOM2=Select[lag,Count[#,TR[___,DD[u,0][_],___,DD[u,0][_],___],99]>0&]//showLength;
lagCOM3=Select[lag,Count[#,TR[___,DD[fp,0][__],___],99]>0&]//showLength;

lagCOM1=lagCOM1;(*looks for single element*)
lagCOM2=lagCOM2//rotateTraces;
lagCOM3=lagCOM3//rotateTraces;


(* ::Text:: *)
(*Get the operator relations*)


fullCOM1=getRelationsFromRule[lagCOM1,ruleCOM1,tagCOM1,DD]//showLength//showTiming;
fullCOM2a=getRelationsFromRule[lagCOM2,ruleCOM2a,tagCOM2a,TR]//showLength//showTiming;
fullCOM3a=getRelationsFromRule[lagCOM3,ruleCOM3a,tagCOM3a,TR]//showLength//showTiming;
fullCOM2b=getRelationsFromRule[lagCOM2,ruleCOM2b,tagCOM2b,TR]//showLength//showTiming;
fullCOM3b=getRelationsFromRule[lagCOM3,ruleCOM3b,tagCOM3b,TR]//showLength//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullCOM1,fullCOM2a,fullCOM3a,fullCOM2b,fullCOM3b]//reshapeTerms//showTiming;
relCOM=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[CH] Cayley-Hamilton (nf=2,3)*)


(* ::Text:: *)
(*Takes 35' (p8) / 5s (p6)*)


(* ::Text:: *)
(*Expand the terms such that the traces appear in any possible order (rotateTraces). *)
(*Then surround the first 2 (3) matrices, for nf = 2 (3), with a List. The CH relation will be applied on those groups.*)


lagCH=lag//rotateTraces//showLength;

lagGroupedNf2=(lagCH//separateArgsTR[2])/.Plus->List//Flatten//showTiming//showLength;
lagGroupedNf2=%//sortGroupsCH//DeleteDuplicates//showLength;

lagGroupedNf3=(lagCH//separateArgsTR[3])/.Plus->List//Flatten//showTiming//DeleteDuplicates//showLength;
lagGroupedNf3=%//sortGroupsCH//DeleteDuplicates//showLength;


(* ::Text:: *)
(*Define the CH trace identities for nf=2,3*)


ruleCHNf2=tagX[{B__},{C__},Z___]:>TR[B,C,Z]+TR[C,B,Z]-TR[B,TR[C],Z]-TR[C,TR[B],Z]-TR[TR[B,C],Z]+TR[TR[B],TR[C],Z];
tagCHNf2[tag_]:=TR[{B__},{C__},Z___]:>tag[{B},{C},Z] /;i++<1;

ruleCHNf3=tagX[{B__},{C__},{D__},Z___]:>
TR[B,C,D,Z]+TR[D,B,C,Z]+TR[C,B,D,Z]+TR[D,C,B,Z]+TR[C,D,B,Z]+TR[B,D,C,Z]-TR[D,B,TR[C],Z]-
TR[B,D,TR[C],Z]-TR[B,C,TR[D],Z]-TR[C,B,TR[D],Z]-TR[D,C,TR[B],Z]-TR[C,D,TR[B],Z]-TR[D,TR[B,C],Z]-
TR[B,TR[C,D],Z]-TR[C,TR[B,D],Z]-TR[TR[B,C,D],Z]-TR[TR[C,B,D],Z]+TR[D,TR[B],TR[C],Z]+TR[B,TR[C],TR[D],Z]+
TR[C,TR[B],TR[D],Z]+TR[TR[D],TR[B,C],Z]+TR[TR[B],TR[C,D],Z]+TR[TR[C],TR[B,D],Z]-TR[TR[B],TR[C],TR[D],Z];
tagCHNf3[tag_]:=TR[{B__},{C__},{D__},Z___]:>tag[{B},{C},{D},Z] /;i++<1;

checkRule[tagCHNf2,ruleCHNf2];
checkRule[tagCHNf3,ruleCHNf3];


(* ::Text:: *)
(*Get operator relations*)


fullCHNf2=getRelationsFromRule[ lagGroupedNf2,ruleCHNf2,tagCHNf2,TR]/.Nf->2//showTiming;
fullCHNf3=getRelationsFromRule[ lagGroupedNf3,ruleCHNf3,tagCHNf3,TR]/.Nf->3//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullCHNf2//reshapeTerms//showTiming;
relCH[2]=%//identifyTerms//deleteDuplicatesSign//showLength;


fullCHNf3//reshapeTerms//showTiming;
relCH[3]=%//identifyTerms//deleteDuplicatesSign//showLength;


Do[relCH[i]={},{i,4,100}]


(* ::Subsection::Closed:: *)
(*Reorder operators*)


(*import["P8/rel"]*)
(*Get[NotebookDirectory[]<>"/save/"<>"P8/rel"<>".mx"]*)


(* ::Subsubsection::Closed:: *)
(*Symmetrize on H and C*)


(* ::Text:: *)
(*(time 1')*)


(* ::Text:: *)
(*Define discrete transformations.*)
(*Find linear combinations of terms that are even under H and eigenvectors of C.*)
(*Define transformation from the symmetric to the raw operator basis. *)


Clear[applyC,applyH]
applyC[terms_]:=(terms/.DD[fp,n_][i___]:>sign DD[fp,n][i])//reverseTR//pullSign//reshapeTermsBare
applyH[terms_]:=(terms/.DD[chim,n_][i___]:>sign DD[chim,n][i]/.I:>-I)//reverseTR//pullSign//reshapeTermsBare

lag//symmetrize[applyH,applyC]//showTiming//showLength;
symToRawOpes=%//identifyTerms//getTransformationRules//showTiming//showLength;
{opesCE,opesCO}=separateEvenOddUnder[applyC][symToRawOpes,lag]//showTiming;



rawToSymOpes=symToRawOpes//getInverseTransformation//showTiming;


(* ::Subsubsection::Closed:: *)
(*Define preferred terms*)


(* ::Text:: *)
(*Define the preferential terms for the final minimal basis.*)


Clear[scorePreferredOperators]
scorePreferredOperators[term_]:=
hasNotHas[term,u,chim|chip|fm|fp]             * 1 +
hasNotHas[term,chim|chip,fm|fp]               * 10^-1 + 
hasNotHas[term,fm|fp,chim|chip]               * 10^-2 + 
hasField[term,fm|fp]*hasField[term,chim|chip] * 10^-3 +
nTraces[term]                   * 10^-4 +
(10 - nFields[term,chim|chip])  * 10^-6 +
(10 - nFields[term,fm|fp])      * 10^-7 +
(10 - nFields[term,u])          * 10^-8 +
(10 - nDer[term])               * 10^-9 +
(10 - nSeqDer[term])            * 10^-10


(*lag[[1;;-1;;100]];lag[[1;;-1;;1000]];
{%,%//Map[scorePreferredOperators]//N//Map[FullForm]}//Transpose//see;*)


(* ::Text:: *)
(*Reorder the terms putting the most preferred terms at the bottom (higher score) such that they are removed last.*)
(*Move C even terms to the beginning of the list so that we can safely neglect C odd operators to accelerate the computation later.*)
(*Invert transformation.*)


lag//reorderOperators[scorePreferredOperators]//identifyTerms;
symToPrefOpes = %//moveUp[opesCE]//getTransformationRulesFromListOrder;
prefToSymOpes = symToPrefOpes//getInverseTransformationNaive;


(* ::Subsubsection::Closed:: *)
(*Convert to functions [import]*)


(* ::Text:: *)
(*Convert rules to functions*)


symToRawOpesF = symToRawOpes // rulesToFunction;
rawToSymOpesF = rawToSymOpes // rulesToFunction;

symToPrefOpesF = symToPrefOpes // rulesToFunction;
prefToSymOpesF = prefToSymOpes // rulesToFunction;


(* ::Subsubsection::Closed:: *)
(*Check scores*)


(*lag//reorderOperators[scorePreferredOperators];
{%,%//scorePreferredOperators//N//Map[FullForm]}//Transpose//see;*)

(*(ope/@Range[402])/.prefToSymOpes/.ope[i_]\[RuleDelayed]lag[[i]]//Reverse;*)


(* ::Subsection::Closed:: *)
(*Reduce to minimal basis*)


(* ::Text:: *)
(*Time 5' (for all Nf = 2,3,Nf)*)


(* ::Text:: *)
(*Now we put together all the previous results of the calculation to do the reduction to a minimal basis, based on the relations we found.*)
(**)
(*First we transform the relations (in the raw basis) into the proper orderings (pref basis). Optionally, remove C odd operators beforehand to speed up. And build a relation matrix with the operator relations. *)
(**)
(*Gaussian Elimination is performed. In particular the relation matrix is decomposed into a unitary (Q) and an upper triangular (R)  matrix with getMinimalBasis, which uses the third-party code SuiteSparseQR, written in C++.*)
(**)
(*The transformations are undone to be able to read the terms of the final basis.*)
(**)


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->8;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisEvenNf = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;

relationMatrixNf = relationMatrix;


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->3;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisEvenNf3 = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;

relationMatrixNf3 = relationMatrix;


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->2;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisEvenNf2 = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;

relationMatrixNf2 = relationMatrix;


(* ::Subsubsection::Closed:: *)
(*Time*)


Now-START


(* ::Subsubsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/P8.mx",
{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH,
lag, lagShapes, lagShapesZeroes, opesCE, opesCO,
rawToSymOpes, symToPrefOpes, prefToSymOpes, symToRawOpes, rawOpesToTerms,
relationMatrixNf2,relationMatrixNf3,relationMatrixNf,
miniBasisEvenNf3,miniBasisEvenNf2,miniBasisEvenNf
}];


(* ::Subsection::Closed:: *)
(*Remove contact terms from full basis*)


(* ::Subsubsection:: *)
(*Mixed notation*)


Clear[cal]
cal[expr_]:=expr/.
{fm:>SuperMinus[\[ScriptF]],fp:>SuperPlus[\[ScriptF]],chim:>SuperMinus[\[Chi]],chip:>SuperPlus[\[Chi]],u:>\[ScriptU]}/.
{FL:>F^L,FR:>F^R,chi-> \[Chi],chid-> SuperDagger[\[Chi]],chit-> \!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\),chitd-> SuperDagger[\!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\)],U->U,Ud-> SuperDagger[U]}


(* ::Subsubsection:: *)
(*Import contact terms*)


import["P8contactBasisNf2"]
contactTerms//see;


(* ::Subsubsection:: *)
(*Reobtain minimal basis with contact terms*)


contactOpe = relationMatrixNf2//additionalOpesFor[contactTerms];
contactOpeToTerms = #/.MapThread[Rule,{contactOpe,contactTerms}] &;
contactRelations= contactTerms//toSmallUBasis//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF//contactOpe - # &;

{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->2;
extendedRelationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] //Append[contactRelations] //getRelationMatrix;
extendedRelationMatrix//MatrixPlot

miniBasisFull = extendedRelationMatrix // getMinimalBasis //showTiming //contactOpeToTerms// prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

summary[miniBasisFull,{Identity}, 
 (chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;


"Contact terms LR basis"
Complement[miniBasisFull,miniBasisEvenNf2]//see;

"Terms removed from small-u basis"
Complement[miniBasisEvenNf2,miniBasisFull]//see;



(*(*Slightly more elegant solution using the relation matrix. Not done*)

contactOpe = relationMatrixNf2//additionalOpesFor[contactTerms]
contactOpeToTerms = #/.MapThread[Rule,{contactOpe,contactTerms}] &;
contactRelations= contactTerms//toSmallUBasis//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF//contactOpe - # &

extendedRelationMatrix = relationMatrix//appendRelationMatrix[contactRelations//getRelationMatrix]
extendedRelationMatrix // MatrixPlot

miniBasisFull = extendedRelationMatrix // getMinimalBasis //showTiming //contactOpeToTerms// prefToSymOpesF// symToRawOpesF // rawOpesToTerms*)


(* ::Subsubsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/dummyname.mx",
{miniBasisFull
}];


(* ::Subsubsection::Closed:: *)
(*Time*)


Now-START


(* ::Chapter::Closed:: *)
(*ChPT: anomalous sector. U basis. Contact terms. Order p^6-p^8*)


START=Now;


(* ::Subsection::Closed:: *)
(*Configuration*)


(* ::Subsubsection::Closed:: *)
(*Compose terms (fields, symmetries, indices)*)


(* ::Text:: *)
(*Define the building blocks (BB). Each has a number of indices, p power, and number of Us*)


Clear[BB]
BB[NF_]:=Module[{},

fields = {chi,chid,chit,chitd,FL,FR,der,U,Ud};
dim = {p^2,p^2,p^(2*NF-2),p^(2*NF-2),p^2,p^2,p^1,p^0,p^0};
indices = {0,0,0,0,2,2,1,0,0}//Map[in^#&];
countU = {0,0,0,0,0,0,0,1,1}//Map[n^#&];

fields*dim*indices*countU];

BB[2]


(*AUTO: Define nIndices for later*)
Do[nIndices[fields[[i]]] = Exponent[indices[[i]],in] ,{i,Length[fields]}];


(* ::Text:: *)
(*Get combinations of BB specifying which p^n order, number of indices, and if even / odd intrinsic parity*)


Clear[getCombinationsWithSymmetries]
getCombinationsWithSymmetries[order_,nindices_List,NF_,maxU_]:=Module[{combs,maxFields},

maxFields = 8;

combs=Map[getCombinations[BB[NF],#]&,Range[2,maxFields] ]//Flatten;

combs=combs//Cases[#,p^order  _]& ;
combs=combs//Cases[#,a_/; MemberQ[nindices, Exponent[a, in]]]&;
combs=combs//Cases[#,a_/; Exponent[a, n]<=maxU]&;
combs//clearRegulators//DeleteCases[der^_]
]

Clear[clearRegulators]
clearRegulators[exp_]:=exp/.{in->1,p->1,n->1}


(* ::Text:: *)
(*Indices*)


mIndices={m1,m2,m3,m4};
jIndices={j1,j2};

isM=MemberQ[mIndices,#]&;
isJ=MemberQ[jIndices,#]&;

Clear[nPairs]
nPairs[expr_]:=Which[!FreeQ[expr,j2],2,!FreeQ[expr,j1],1,0==0,0]


(* ::Subsubsection::Closed:: *)
(*Readable notation*)


(* ::Text:: *)
(*Define calligraphic symbols with only superscripts. Indices will be subscripts*)


Clear[cal]
cal[expr_]:=expr/.{FL:>F^L,FR:>F^R,chi-> \[Chi],chid-> SuperDagger[\[Chi]],chit-> \!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\),chitd-> SuperDagger[\!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\)],U->U,Ud-> SuperDagger[U]}

(*TR[DD[FL,0][a,j[3]]]*TR[DD[chi,0][],DD[chid,2][c,j[1]],DD[FR,0][k,m[3]],DD[U,2][x,y,z]]
%//readableNotation*)


(* ::Subsubsection::Closed:: *)
(*Chiral invariance*)


Clear[chiralTransform,keepChiralInvariant]

chiralTransform[expr_]:=
expr/.DD[f_,n_][ind___]:>(Switch[f,
chi,seq[R,DD[f,n][ind],L],
chit,seq[R,DD[f,n][ind],L],
chid,seq[L,DD[f,n][ind],R],
chitd,seq[L,DD[f,n][ind],R],
FL, seq[L,DD[f,n][ind],L],
FR,seq[R,DD[f,n][ind],R],
U,seq[R,DD[f,n][ind],L],
Ud,seq[L,DD[f,n][ind],R]])/.seq[a__]:>Sequence[a]

keepChiralInvariant[expr_]:=
chiralTransform[expr]/.TR[a__]:>RotateLeft[TR[a],1]//.
TR[a___,R,R,b___]:>TR[a,b]//.
TR[a___,L,L,b___]:>TR[a,b]/.
TR[___,(R|L),___]:>0


(*We don't need to check that all {groups} of matrices inside a trace transform either under L or R. Just apply chiral invariance inside each group*)

Clear[keepUnmixedLRGroups]
keepUnmixedLRGroups[expr_]:=
Map[ (*can't be applied directly to single terms. always lists*)
#/.{a__}:>RotateLeft[{a},1]//.
{a___,R,R,b___}:>{a,b}//.
{a___,L,L,b___}:>{a,b}/.
{___,(R|L),___}:>0/.
TR[___,0,___]:>0//.
(L|R):>Sequence[]&
,expr]



(* ::Subsubsection::Closed:: *)
(*Trivial relations (removeZeroes, generateAlternativeShapes)*)


(* ::Subsubsubsection::Closed:: *)
(*removeEasyZeroes*)


Clear[removeEasyZeroes]
removeEasyZeroes[expr_]:=Module[{aux=expr},
aux=If[zeroTrF,aux//removeTrF,aux];
aux=aux//removeAntisymF]


(* ::Text:: *)
(*Tr[f] = 0*)


Clear[removeTrF]
removeTrF[expr_]:=expr/.TR[DD[f:(FL|FR),_][__]]:>0


(* ::Text:: *)
(*f_aa=0*)


Clear[removeAntisymF]
removeAntisymF[expr_]:=expr/.TR[___,DD[f:(FL|FR),n_][___,j_,j_],___]:>0


(* ::Subsubsubsection::Closed:: *)
(*generateAlternativeShapes*)


Clear[generateAlternativeShapesUnsigned]
generateAlternativeShapesUnsigned[term_]:=Module[{aux=term},
aux=aux//rotationsOfTR;
aux=aux//Map[swapIndicesF]//Flatten//ignoreSigns;
aux=aux//Map[swapDummyIndices[Sequence@@jIndices]]//Flatten;
aux=aux/.Times[_?NumericQ,rest__]:>Times[rest];

(*Here we also permute m indices, only possible for short lists*)
aux=aux//Map[shuffleIndicesEps]//Flatten;

aux=aux//ignoreSigns//DeleteDuplicates;
PrependTo[aux,term] (*Keep the original term in first possition*)
]


Clear[generateAlternativeShapesSigned] (*With LeviCivita!*)
generateAlternativeShapesSigned[term_]:=Module[{aux=term},
aux=aux//rotationsOfTR;
aux=aux//Map[swapIndicesF]//Flatten;
aux=aux//Map[swapDummyIndices[Sequence@@jIndices]]//Flatten;
aux=aux/.Times[nn_?NumericQ,rest__]:>Times[rest];

(*Here we also permute m indices, only possible for short lists*)
aux=aux//Map[shuffleIndicesEps]//Flatten;

aux=aux//pullSign//simplifySign;
PrependTo[aux,term] (*Keep the original term in first possition*)
]


(* ::Text:: *)
(*Ways of rewriting terms*)


Clear[rotationsOfTR,allCyclicRotations]

rotationsOfTR[expr_]:=(expr/.TR[a___]:>(Plus@@allCyclicRotations[TR[a]])//.
TR[a___,x_+y_,b___]:>TR[a,x,b]+TR[a,y,b]//Expand//plusToList)/.Times[_?NumericQ,rest__]:>Times[rest]

allCyclicRotations[expr_]:=Map[RotateRight[expr,#]&,Range[Length[expr]]]

Clear[swapIndicesF]
swapIndicesF[expr_]:=expr/.DD[f:(FL|FR),n_][i___,x_,y_]:>DD[f,n][i,x,y]+sign DD[f,n][i,y,x]/;x=!=y//.TR[a___,x_+y_,b___]:>TR[a,x,b]+TR[a,y,b]//Expand//plusToList;

Clear[swapDummyIndices]
swapDummyIndices[ind__][term_]:=Join[{term},Table[term/.swap,{swap,{#[[1]]->#[[2]], #[[2]]->#[[1]]}& /@Subsets[{ind}[[1;;nPairs[term]]],{2}]}]]


(* ::Text:: *)
(*Levi-Civita antisymmetric permutations*)


Clear[shuffleIndicesEps]
shuffleIndicesEps[expr_]:=Module[{aux=expr,pos,permIndices,permSigns},
pos=Position[expr,_?(isM)];If[pos=={},Return[{expr}]];

permIndices=Permutations[mIndices];
permSigns=Signature/@permIndices /. -1 ->sign;

Table[permSigns[[i]]*ReplaceAll[aux,MapThread[Rule,{mIndices,permIndices[[i]]}]],{i,Length[permIndices]}]
]


(* ::Subsubsubsection::Closed:: *)
(*orderFields*)


Clear[orderFields]
orderFields[expr_?(Head@Head@#===DD&)]:=expr/.DD[f_,n_][ind___]:>(Switch[f,
U,10+n,
chi,20+n,
chit,30+n,
chid,40+n,
chitd,50+n,
FL,60+n,
FR,70+n]
-0.1*Length[Cases[{ind},_?isJ,99]]
-0.01*Total@Total[Position[{ind}[[1;;n]],_?isJ]])


(* ::Subsubsection::Closed:: *)
(*Operator relations*)


(* ::Subsubsubsection::Closed:: *)
(*TD*)


(* ::Text:: *)
(*Needed to substitute indices a,b,c,d,... when building TD relations. Cannot be in Core functions bc depends on mIndices and jIndices. And I think that substituting it with a function would make it slower....*)


Clear[subsInd2,subsInd4,subsInd6,subsInd8]

subsInd2={};
subsInd4=Inner[ReverseApplied[Rule],indPerm[4],{x,a,b,c},List];
subsInd6=Inner[ReverseApplied[Rule],indPerm[6],{x,a,b,c,d,e},List];
subsInd8=Inner[ReverseApplied[Rule],indPerm[8],{x,a,b,c,d,e,f,g},List];


(* ::Subsection::Closed:: *)
(*Options*)


ORDER=8;
zeroTrF=True;
NF=2;

maxU=0;


(* ::Subsection::Closed:: *)
(*Construct possible terms*)


(* ::Text:: *)
(*Keep p^n terms. 4, 6, or 8 indices. Odd intrinsic parity.*)
(*Introduce derivatives.*)
(*Introduce traces.*)
(*Introduce indices.*)


getCombinationsWithSymmetries[ORDER,{4,6,8},NF,maxU]//showLength;
%//Map[applyDerivativesAndPermutations]//showLengthFlat;
%//introduceTraces//showLengthFlat;
%//insertIndexPlaceHolders//Map[insertIndices];
possibleTerms=%//Flatten//keepChiralInvariant//DeleteCases[0]//showLength;


(* ::Subsection::Closed:: *)
(*Trivial relations*)


(* ::Subsubsection:: *)
(*Main*)


(* ::Text:: *)
(*Reduce the list of possibleTerms accounting for obvious zeroes.*)
(*Then generate all ways of writing the terms to find duplicates (ignoring signs).*)
(*Then remove vanishing terms due to symmetric x antisymmetric indices.*)


possibleTerms//removeEasyZeroes//keepChiralInvariant//DeleteCases[0]//showLength;
lagWithZeroes = %//Map[generateAlternativeShapesUnsigned]//Map[Sort]//Map[First]//DeleteDuplicates//showTiming//showLength;
lagRandomShapes = %//Map[generateAlternativeShapesSigned]//Map[DeleteDuplicates]//ignoreSigns//Select[DuplicateFreeQ]//Map[First]//showTiming//showLength;


(* ::Text:: *)
(*Build functions to rewrite terms into standard shape*)


(*removeSymAntisymZeroesDict*)
Complement[lagWithZeroes,lagRandomShapes]//Map[generateAlternativeShapesUnsigned]//showTiming//showLengthFlat;
removeSymAntisymZeroesDict = %//Map[getDictionaryOfShapes]//landRulesOnZero//Flatten//rulesToFunction;

(*standardizeShapesDict*)
lag=lagRandomShapes;
lag//Map[generateAlternativeShapesSigned]//showTiming//showLengthFlat;
%//Map[getDictionaryOfShapes]//Flatten;
standardizeShapesDict =%//rulesToFunction;


(* ::Text:: *)
(*Basic test*)


possibleTerms//removeEasyZeroes//keepChiralInvariant//DeleteCases[0]//showLength;
%//removeSymAntisymZeroesDict//DeleteCases[0]//showLength;
%//standardizeShapesDict//ignoreSigns//deleteDuplicatesSign//showLength;


(* ::Text:: *)
(*Wrapper to simplify the code later*)


Clear[reshapeTerms,reshapeTermsBare]
reshapeTerms[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//addSigns//DeleteCases[0]//deleteDuplicatesSign;
reshapeTermsBare[expr_]:=expr//removeEasyZeroes//removeSymAntisymZeroesDict//DeleteCases[0]//standardizeShapesDict//addSigns//DeleteCases[0];


(* ::Subsubsection:: *)
(*Identify terms*)


(* ::Text:: *)
(*Create function that will identify the terms and substitute them by ope[i], where i is the position of the term in 'lag'. Only works after standardizeShapes has been applied.*)


lagDictionary=PositionIndex[lag];
lagScores=lag//Map[termScore];

Clear[identifyTerms]
identifyTerms = makeIdentifyTerms[lag,lagDictionary,lagScores];


(* ::Text:: *)
(*The inverse function can be useful to inspect the final relations. It is used in the last part of the example, "Reduce to minimal basis"*)


Clear[rawOpesToTerms]
rawOpesToTerms[expr_]:=expr/.ope[i_]:>lag[[i]];


(* ::Text:: *)
(*Test*)


lag//identifyTerms//showTiming;
%/.ope[n_]:>n//Total
Range[Length[lag]]//Total


(* ::Subsection::Closed:: *)
(*Operator relations*)


(* ::Subsubsection::Closed:: *)
(*[TD] Total derivatives*)


(* ::Text:: *)
(*Generate anew all terms with 3/5/7 indices (called a,b,c,...) with odd intrinsic parity at O(p7/p5) *)


test=getCombinationsWithSymmetries[ORDER-1,{3,5,7},NF,maxU];
%//Map[applyDerivativesAndPermutations]//introduceTraces;
%//insertIndexPlaceHolders//Flatten//showLength;
termsp7=%//Map[insertOneIndexCombination[#,{a,b,c,d,e,f,g}]&];


(* ::Text:: *)
(*Take the total derivative of each term, adding the 8th/6th/4th index (called x), and distribute the derivative over the product.*)
(*Then replace indices by the usual names (m1, m2. m3, m4, j1, j2). Relations are obtained as linear combinations of ope[i] that are equal to zero.*)


termsp7//Map[Dx];
fullTD=%//keepChiralInvariant//DeleteCases[0]//Map[subsIndices[#,subsInd4,subsInd6,subsInd8]&]//Flatten//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. Store relations in relTD.*)


fullTD//reshapeTerms//showTiming//showLength;
relTD=%//identifyTerms//deleteDuplicatesSign//showLength;


relTD//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[BI] Bianchi identities*)


(* ::Text:: *)
(*Define the identities*)


ruleBIFL=tagX[FL,1][a_,b_,c_]:>DD[FL,1][a,b,c] +DD[FL,1][b,c,a]+DD[FL,1][c,a,b];
ruleBIFR=tagX[FR,1][a_,b_,c_]:>DD[FR,1][a,b,c] +DD[FR,1][b,c,a]+DD[FR,1][c,a,b];

tagBIFL[tag_]:=DD[FL,1][a_,b_,c_]:>tag[FL,1][a,b,c] /;i++<1;
tagBIFR[tag_]:=DD[FR,1][a_,b_,c_]:>tag[FR,1][a,b,c] /;i++<1;
checkRule[tagBIFL,ruleBIFL];
checkRule[tagBIFR,ruleBIFR];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules*)


lagBI=lag//find[FL|FR];


(* ::Text:: *)
(*Get the operator relations*)


fullBIFL=getRelationsFromRule[lagBI,ruleBIFL,tagBIFL,DD]//showTiming;
fullBIFR=getRelationsFromRule[lagBI,ruleBIFR,tagBIFR,DD]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullBIFR,fullBIFL]//reshapeTerms//showTiming;
relBI=%//identifyTerms//deleteDuplicatesSign//showLength;


relBI//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


544/2


(* ::Subsubsection::Closed:: *)
(*[COM] Commutation of derivatives*)


(* ::Text:: *)
(*Define the identities*)


Clear[a,b,c,A,B]


Clear[chiralFMatricesOf]
chiralFMatricesOf[X]:={FXL,FXR}
chiralFMatricesOf[X_]:= chiralTransform[TR[DD[X,0][]]]/.TR[T1_,aa_,T2_]:>{T1,T2}/.{L->FL,R->FR}
(*chiralFMatricesOf[chi]*)

tagCOM[tag_]:=DD[X_,n_?(#>=2&)][ind___]:>tag[X,n][ind] /;i++<1;
ruleCOM=tagX[X_,n_?(#>=2&)][a_,b_,ind___]:>(
{F1,F2}=chiralFMatricesOf[X];
DD[X,n][a,b,ind] -
DD[X,n][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n-2][ind]]-
ii*seq[DD[X,n-2][ind],DD[F2,0][a,b]]);

checkRule[tagCOM,ruleCOM]


tagCOM2[tag_]:=TR[DD[F:(FR|FL),0][a_,b_],DD[X_,n_?(#>=0&)][ind___],A___]:>tag[DD[F,0][a,b],DD[X,n][ind],A]/;i++<1;
ruleCOM2=tagX[DD[F:(FR|FL),0][a_,b_],DD[X_,n_?(#>=0&)][ind___],A___]:>(
{F1,F2}=chiralFMatricesOf[X];
TR[(DD[X,n+2][a,b,ind] -
DD[X,n+2][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n][ind]]-
ii*seq[DD[X,n][ind],DD[F2,0][a,b]]),A]);



tagCOM3[tag_]:=TR[DD[X_,n_?(#>=0&)][ind___],DD[F:(FR|FL),0][a_,b_],A___]:>tag[DD[X,n][ind],DD[F,0][a,b],A]/;i++<1;
ruleCOM3=tagX[DD[X_,n_?(#>=0&)][ind___],DD[F:(FR|FL),0][a_,b_],A___]:>(
{F1,F2}=chiralFMatricesOf[X];
TR[(DD[X,n+2][a,b,ind] -
DD[X,n+2][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n][ind]]-
ii*seq[DD[X,n][ind],DD[F2,0][a,b]]),A]);


(* ::Text:: *)
(*Preselect terms*)


lagCOM=Select[lag,Count[#,DD[_,n_?(#>=2&)][ind__],99]>= 1&]//showLength;
lagCOMall=lag//rotateTraces;


(* ::Text:: *)
(*Get the operator relations*)


fullCOM1=getRelationsFromRule[lagCOM,ruleCOM,tagCOM,DD]//showLength//showTiming;
fullCOM2=getRelationsFromRule[lagCOMall,ruleCOM2,tagCOM2,TR]//showLength//showTiming;
fullCOM3=getRelationsFromRule[lagCOMall,ruleCOM3,tagCOM3,TR]//showLength//showTiming;


Join[fullCOM1,fullCOM2,fullCOM3]//reshapeTerms//showTiming//showLength;
relCOM=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullCOM//reshapeTerms//showTiming;
relCOM=%//identifyTerms//deleteDuplicatesSign//showLength;


relCOM//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsubsection::Closed:: *)
(*[REMOVE?] Test to erase extra term*)


(* ::Text:: *)
(*Remove ? I think it only has the development  of ruleCOM2 and 3*)


(* ::Subsubsubsubsection::Closed:: *)
(*Original*)


(* ::Text:: *)
(*Original*)


(*tagCOM[tag_]:=DD[X_,n_?(#>=2&)][ind___]:>tag[X,n][ind] /;i++<1;

ruleCOM=tagX[X_,n_?(#>=2&)][a_,b_,ind___]:>(
chiralTransform[TR[DD[X,0][]]]/.TR[T1_,aa_,T2_]:>(
If[T1===R,MAT1=FR,MAT1=FL];
If[T2===R,MAT2=FR,MAT2=FL];{});
DD[X,n][a,b,ind] -
DD[X,n][b,a,ind]  + 
ii*seq[DD[MAT1,0][a,b],DD[X,n-2][ind]]-
ii*seq[DD[X,n-2][ind],DD[MAT2,0][a,b]]);*)


(*checkRule[tagCOM,ruleCOM];*)


(* ::Text:: *)
(*Just applying the identity*)


(*{I TR[DD[chi,0][],DD[chitd,4][m1,m2,m3,m4]],-I TR[DD[chid,0][],DD[chit,4][m1,m2,m3,m4]]}//see;
%/.(ruleCOM/.tagX->DD)//see;
%//cleanTraces//see;
%/.ii:>I//Simplify//see;
%//reshapeTerms//see;*)


(* ::Subsubsubsubsection::Closed:: *)
(*Make the change*)


(* ::Text:: *)
(*Get inspiration from above.*)
(*Rotate traces. Identify the first term*)
(**)


(*Original of small - u*)


(*Clear[a,b,c,A,B]

ruleCOM1=tagX[X_,n_?(#>=2&)][a_,b_,ind___]:>
-DD[X,n][a,b,ind] +DD[X,n][b,a,ind]  +
(1/4)*(
seq[DD[u,0][a],DD[u,0][b],DD[X,n-2][ind]] -
 seq[DD[u,0][b],DD[u,0][a],DD[X,n-2][ind]]) -( ii/2) seq[DD[fp,0][a,b],DD[X,n-2][ind]]- 
(1/4)*(
seq[DD[X,n-2][ind],DD[u,0][a],DD[u,0][b]] - 
seq[DD[X,n-2][ind],DD[u,0][b],DD[u,0][a]]) + ( ii/2) seq[DD[X,n-2][ind],DD[fp,0][a,b]];

tagCOM1[tag_]:=DD[X_,n_?(#>=2&)][ind___]:>tag[X,n][ind] /;i++<1;

ruleCOM2a=tagX[DD[u,0][a_],DD[u,0][b_],DD[X_,n_?(#>=0&)][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM2a[tag_]:=TR[DD[u,0][a_],DD[u,0][b_],DD[X_,n_][ind___],A___]:>tag[DD[u,0][a],DD[u,0][b],DD[X,n][ind],A]/;i++<1;

ruleCOM3a=tagX[DD[fp,0][a_,b_],DD[X_,n_][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM3a[tag_]:=TR[DD[fp,0][a_,b_],DD[X_,n_][ind___],A___]:>tag[DD[fp,0][a,b],DD[X,n][ind],A]/;i++<1;

(*Not necesary 2b and 3b: 9331 rel anyway*)
ruleCOM2b=tagX[DD[X_,n_][ind___],DD[u,0][a_],DD[u,0][b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM2b[tag_]:=TR[DD[X_,n_][ind___],DD[u,0][a_],DD[u,0][b_],A___]:>tag[DD[X,n][ind],DD[u,0][a],DD[u,0][b],A]/;i++<1;

ruleCOM3b=tagX[DD[X_,n_][ind___],DD[fp,0][a_,b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
tagCOM3b[tag_]:=TR[DD[X_,n_][ind___],DD[fp,0][a_,b_],A___]:>tag[DD[X,n][ind],DD[fp,0][a,b],A]/;i++<1;

checkRule[tagCOM1,ruleCOM1];
checkRule[tagCOM2a,ruleCOM2a];
(*In this case the other rules are a bit too general to be checked*)*)


(*Changes....


Clear[chiralFMatricesOf]
chiralFMatricesOf[X]:={FXL,FXR}
chiralFMatricesOf[X_]:= chiralTransform[TR[DD[X,0][]]]/.TR[T1_,aa_,T2_]:>{T1,T2}/.{L->FL,R->FR}
(*chiralFMatricesOf[chi]*)

tagCOM[tag_]:=DD[X_,n_?(#>=2&)][ind___]:>tag[X,n][ind] /;i++<1;
ruleCOM=tagX[X_,n_?(#>=2&)][a_,b_,ind___]:>(
{F1,F2}=chiralFMatricesOf[X];
DD[X,n][a,b,ind] -
DD[X,n][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n-2][ind]]-
ii*seq[DD[X,n-2][ind],DD[F2,0][a,b]]);
*)


(*tagCOM2[tag_]:=TR[DD[F:(FR|FL),0][a_,b_],DD[X_,n_?(#>=0&)][ind___],A___]:>tag[DD[F,0][a,b],DD[X,n][ind],A]/;i++<1;
ruleCOM2=tagX[DD[F:(FR|FL),0][a_,b_],DD[X_,n_?(#>=0&)][ind___],A___]:>(
{F1,F2}=chiralFMatricesOf[X];
TR[(DD[X,n+2][a,b,ind] -
DD[X,n+2][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n][ind]]-
ii*seq[DD[X,n][ind],DD[F2,0][a,b]]),A]);
*)


(*tagCOM3[tag_]:=TR[DD[X_,n_?(#>=0&)][ind___],DD[F:(FR|FL),0][a_,b_],A___]:>tag[DD[X,n][ind],DD[F,0][a,b],A]/;i++<1;
ruleCOM3=tagX[DD[X_,n_?(#>=0&)][ind___],DD[F:(FR|FL),0][a_,b_],A___]:>(
{F1,F2}=chiralFMatricesOf[X];
TR[(DD[X,n+2][a,b,ind] -
DD[X,n+2][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n][ind]]-
ii*seq[DD[X,n][ind],DD[F2,0][a,b]]),A]);*)


(*{
TR[DD[FR,3][a,b,x,y,z]],
TR[DD[chitd,2][a,b]]
}//see;
%/.(ruleCOM/.tagX->DD)//see;

{
TR[DD[FR,0][a,b],DD[chi,0][c,d]],
TR[DD[FR,0][a,b],DD[FR,0][c,d]]
}//see;
%/.(ruleCOM2/.tagX->TR)//see;*)


(*{TR[DD[chi,0][a,b],DD[chid,0][c,d],DD[FR,0][x,y]]}//rotateTraces//see;
%/.(ruleCOM3/.tagX->TR)//see//cleanTraces//reshapeTerms//see;
%%/.(ruleCOM2/.tagX->TR)/.ii:>I//see//cleanTraces//reshapeTerms//see;
*)


(* ::Subsubsection::Closed:: *)
(*[SCH] Schouten identity*)


(* ::Text:: *)
(*Preselect terms of the basis and get relations*)


lagSCH=Select[lag,nPairs[#]>0&]//showLength;
fullSCH=lagSCH//Map[getRelationSCH4m]//Flatten//DeleteDuplicates//showTiming//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullSCH//reshapeTerms//showTiming;
relSCH=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[CH] Cayley-Hamilton (nf=2,3)*)


(* ::Text:: *)
(*Expand the terms such that the traces appear in any possible order (rotateTraces). *)
(*Then surround the first 2 (3) matrices, for nf = 2 (3), with a List. The CH relation will be applied on those groups.*)


lagCH=lag//rotateTraces//showLength;

lagGroupedNf2=(lagCH//separateArgsTR[2])/.Plus->List//Flatten//showTiming//showLength;
lagGroupedNf2=%//sortGroupsCH//DeleteDuplicates//showLength;
lagGroupedNf2=%//chiralTransform//keepUnmixedLRGroups//DeleteCases[0]//showLength;

lagGroupedNf3=(lagCH//separateArgsTR[3])/.Plus->List//Flatten//showTiming//DeleteDuplicates//showLength;
lagGroupedNf3=%//sortGroupsCH//DeleteDuplicates//showLength;
lagGroupedNf3=%//chiralTransform//keepUnmixedLRGroups//DeleteCases[0]//showLength;



(* ::Text:: *)
(*Define the CH trace identities for nf=2,3*)


ruleCHNf2=tagX[{B__},{C__},Z___]:>TR[B,C,Z]+TR[C,B,Z]-TR[B,TR[C],Z]-TR[C,TR[B],Z]-TR[TR[B,C],Z]+TR[TR[B],TR[C],Z];
tagCHNf2[tag_]:=TR[{B__},{C__},Z___]:>tag[{B},{C},Z] /;i++<1;

ruleCHNf3=tagX[{B__},{C__},{D__},Z___]:>
TR[B,C,D,Z]+TR[D,B,C,Z]+TR[C,B,D,Z]+TR[D,C,B,Z]+TR[C,D,B,Z]+TR[B,D,C,Z]-TR[D,B,TR[C],Z]-
TR[B,D,TR[C],Z]-TR[B,C,TR[D],Z]-TR[C,B,TR[D],Z]-TR[D,C,TR[B],Z]-TR[C,D,TR[B],Z]-TR[D,TR[B,C],Z]-
TR[B,TR[C,D],Z]-TR[C,TR[B,D],Z]-TR[TR[B,C,D],Z]-TR[TR[C,B,D],Z]+TR[D,TR[B],TR[C],Z]+TR[B,TR[C],TR[D],Z]+
TR[C,TR[B],TR[D],Z]+TR[TR[D],TR[B,C],Z]+TR[TR[B],TR[C,D],Z]+TR[TR[C],TR[B,D],Z]-TR[TR[B],TR[C],TR[D],Z];
tagCHNf3[tag_]:=TR[{B__},{C__},{D__},Z___]:>tag[{B},{C},{D},Z] /;i++<1;

checkRule[tagCHNf2,ruleCHNf2];
checkRule[tagCHNf3,ruleCHNf3];


(* ::Text:: *)
(*Get operator relations*)


fullCHNf2=getRelationsFromRule[ lagGroupedNf2,ruleCHNf2,tagCHNf2,TR]/.Nf->2//showTiming;
fullCHNf3=getRelationsFromRule[ lagGroupedNf3,ruleCHNf3,tagCHNf3,TR]/.Nf->3//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullCHNf2//reshapeTerms//showTiming;
relCH[2]=%//identifyTerms//deleteDuplicatesSign//showLength;


fullCHNf3//reshapeTerms//showTiming;
relCH[3]=%//identifyTerms//deleteDuplicatesSign//showLength;


Do[relCH[i]={},{i,4,100}]


(* ::Subsection:: *)
(*Reorder operators*)


(* ::Subsubsection::Closed:: *)
(*Symmetrize on H and C*)


(* ::Text:: *)
(*Define discrete transformations.*)
(*Find linear combinations of terms that are even under H and eigenvectors of C.*)
(*Define transformation from the symmetric to the raw operator basis. MAKE IT FUNCTION ? BETTER *)


Clear[applyC,applyP,applyH]
applyP[terms_]:=(sign*terms/.{chi:>chid,chit:>chitd,chid:>chi,chitd:>chit,FL:>FR,FR:>FL})//reshapeTermsBare//addSigns
applyC[terms_]:=(terms/.{DD[FL,n_][i___]:>sign DD[FR,n][i] , DD[FR,n_][i___]:>sign DD[FL,n][i]})//reverseTR//pullSign//reshapeTermsBare//addSigns
applyH[terms_]:=(terms/.{chi:>chid,chit:>chitd,chid:>chi,chitd:>chit}/.Complex[a_,b_]:>Complex[a,-b])//reverseTR//pullSign//reshapeTermsBare//addSigns

test=lag//showLength//symmetrize[applyH,applyP,applyC]//showTiming//showLength;
symToRawOpes=%//identifyTerms//getTransformationRules//showTiming//showLength;
{opesPCE,opesPCO}=separateEvenOddUnder[applyC,applyP][symToRawOpes,lag]//showTiming;


rawToSymOpes=symToRawOpes//getInverseTransformation//showTiming;


(* ::Text:: *)
(*Convert to function and accelerate with Dispatch*)


symToRawOpesF = symToRawOpes // rulesToFunction;
rawToSymOpesF = rawToSymOpes // rulesToFunction;


(* ::Subsubsection::Closed:: *)
(*Reorder and promote C even terms*)


(* ::Text:: *)
(*Define the preferential the terms for the final minimal basis.*)


Clear[scorePreferredOperators]
scorePreferredOperators = Identity


Clear[scorePreferredOperators]
scorePreferredOperators[term_]:=
nFields[term,DD[chit|chitd,_][__]]                   * 10 +
nTraces[term]                                        * 1 +
nSeqDer[term]                                        * 10^-1 +
hasField[term,FL|FR]*hasField[term,chit|chitd|chi|chid] * 10^-2


(* ::Text:: *)
(*Reorder the terms putting the preferred terms at the bottom (lowest score) such that they are removed last.*)
(*Move C even terms to the beginning of the list so that we can safely neglect C odd operators to accelerate the computation later.*)
(*Invert transformation.*)


lag//reorderOperators[scorePreferredOperators]//identifyTerms;
symToPrefOpes = %//moveUp[opesPCE]//getTransformationRulesFromListOrder;
prefToSymOpes = symToPrefOpes//getInverseTransformationNaive;


(* ::Text:: *)
(*Convert to functions*)


symToPrefOpesF = symToPrefOpes // rulesToFunction;
prefToSymOpesF = prefToSymOpes // rulesToFunction;


(* ::Subsubsection::Closed:: *)
(*Check scores*)


(*lag//reorderOperators[scorePreferredOperators];
{%,%//Map[scorePreferredOperators]//N//Map[FullForm]}//Transpose//see;*)

(*(ope/@Range[402])/.prefToSymOpes/.ope[i_]\[RuleDelayed]lag[[i]]//Reverse;*)


(* ::Subsection::Closed:: *)
(*Reduce to minimal basis*)


(* ::Text:: *)
(*Takes 1' (Nf=8) , *)


(* ::Text:: *)
(*Now we put together all the previous results of the calculation to do the reduction to a minimal basis, based on the relations we found.*)
(**)
(*First we transform the relations (in the raw basis) into the proper orderings (pref basis). Optionally, remove C odd operators beforehand to speed up. And build a relation matrix with the operator relations. *)
(**)
(*Gaussian Elimination is performed. In particular the relation matrix is decomposed into a unitary (Q) and an upper triangular (R)  matrix with getMinimalBasis, which uses the third-party code SuiteSparseQR, written in C++.*)
(**)
(*The transformations are undone to be able to read the terms of the final basis.*)
(**)


{relTD,relBI,relCOM,relSCH,relCH[Nf]} /. Nf->NF;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesPCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisEvenNf2 = summary[miniBasis, {applyC,applyP}, 
1:>1,
(chit | chitd):>0, 
{(FR):>FL}
] 


(* ::Text:: *)
(*Note: avoiding to have mixed terms seems to always bring back the term with 4 derivatives on chi*)


(* ::Input:: *)
(**)


(* ::Subsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/P8contactNf2DUMMY.mx",
{relTD,relBI,relCOM,relSCH,relCH,
lag, lagWithZeroes,lagRandomShapes,
miniBasisEvenNf2
}];

contactTerms=miniBasisEvenNf2;
DumpSave[NotebookDirectory[]<>"/save/P8contactBasisNf2.mx",
{
contactTerms
}];


(* ::Subsection::Closed:: *)
(*Time*)


Now-START
