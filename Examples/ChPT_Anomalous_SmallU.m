(* ::Package:: *)

Quit[]


AppendTo[$Path, ParentDirectory[NotebookDirectory[]]];
Needs["MINIBAR`"]


(* ::Chapter:: *)
(*ChPT: anomalous sector. Small-u basis. Order p^6-p^8*)


START=Now;


(* ::Text:: *)
(*Time*)
(*p^6 - 3s*)
(*p^8 - 12m (i9 64Gb)*)


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


(* ::Subsubsubsection:: *)
(*Insert all permutations*)


(* ::Text:: *)
(*In principle this is REDUNDANT as there is a general MINIBAR function 'insertIndices' (to be tested)*)
(**)
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



(* ::Subsubsubsection::Closed:: *)
(*removeSymAntisymZeroes*)


(* ::Text:: *)
(*This code is REDUNDANT as the same can be achieved with a simpler method as shown in the calculation*)


Clear[removeSymAntisymZeroes]
removeSymAntisymZeroes[expr_]:=Module[{aux=expr},
aux=aux//Map[onTerms[removeSymAntisymJ]];
aux=aux//Map[onTerms[removeSymmtricalOnM]]]


(* ::Text:: *)
(*removeSymAntisymJ: symmetric[j1,j2]  f[j1,j2] = 0*)


Clear[removeSymAntisymJ]

removeSymAntisymJ[0]:=0;
removeSymAntisymJ[expr_]:=If[isSymmetricOnJ[expr]&&!FreeQ[expr,DD[f:(fm|fp),_][___,j1,j2]],0,expr]


(*TR[DD[fm,0][j1,j2],DD[u,0][m1]] TR[DD[u,0][j1],DD[u,0][j2]] TR[DD[u,0][m2],DD[u,0][m3],DD[u,0][m4]];
%//removeSymAntisymJ*)


(* ::Text:: *)
(*removeSymmtricalOnM: antisymmetric permutations of m-indices cannot leave invariant the term*)


(* ::Text:: *)
(*General protocol: swap index pairs or apply odd permutations to 4-tuples  [e.g. {m1,m2} -> {m2,m1} , {m1,m2,m3,m4} -> {m2,m3,m4,m1} ] and sort canonically the term. If it goes back to the original shape, it's symmetrical and antisymmetrical, i.e. it's 0*)


Clear[isSymmetricalOnMPairs,isSymmetricalOn3MSwaps,removeSymmtricalOnM]
removeSymmtricalOnM[expr_]:=If[isSymmetricalOnMPairs[expr]||isSymmetricalOn3MSwaps[expr],0,expr]

isSymmetricalOnMPairs[0]:=True;
isSymmetricalOnMPairs[expr_?(#=!=0&)]:=Module[{input,mpairs,pair,res,answer},
input=expr//sortTracesBare;
mpairs=Subsets[{m1,m2,m3,m4},{2}];
answer=False;
Do[
pair=mpairs[[i]];
res1=input/.{pair[[1]]->pair[[2]],pair[[2]]->pair[[1]]}//sortTracesBare;
res2=input/.{pair[[1]]->pair[[2]],pair[[2]]->pair[[1]]}/.{j1->j2,j2->j1}//sortTracesBare;
If[res1-input===0||res2-input===0,answer=True;Break[],{}],
{i,Length[mpairs]}];
answer
]
(*TR[DD[u,0][j1]] TR[DD[fm,0][j1,m1],DD[u,0][m2]] TR[DD[u,0][m3],DD[u,0][m4]];*)
(*TR[DD[fm,0][j1,j1],DD[u,0][m1],DD[u,0][m2],DD[u,0][m3],DD[u,0][m4]];*)
(*%//isSymmetricalOnMPairs*)

(*Testing all odd permutations. There are 6 permutations with 3 swaps
https://mathworld.wolfram.com/OddPermutation.html*)
isSymmetricalOn3MSwaps[0]:=True;
isSymmetricalOn3MSwaps[expr_?(#=!=0&)]:=Module[{input,res,rule,answer,oddPerm3Swaps},
input=expr//sortTracesBare;
oddPerm3Swaps={{m2,m3,m4,m1},{m2,m4,m1,m3},{m3,m1,m4,m2},{m3,m4,m2,m1},{m4,m1,m2,m3},{m4,m3,m1,m2}};
answer=False;
Do[
rule=MapThread[Rule,{{m1,m2,m3,m4},oddPerm3Swaps[[i]]}];
res1=input/.rule//sortTracesBare;
res2=input/.rule/.{j1->j2,j2->j1}//sortTracesBare;
If[res1-input===0||res2-input===0,answer=True;Break[],{}],
{i,3}];
answer
]



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


(* ::Subsubsection::Closed:: *)
(*Trivial relations (standardizeShapes)*)


(* ::Text:: *)
(*This code is REDUNDANT as the same can be achieved with a simpler method as shown in the calculation*)
(**)
(*See discussion in the section of the main calculation "Trivial relations"*)


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


(* ::Subsubsubsection:: *)
(*[TD] Total derivatives - substitute indices*)


Clear[subsInd4,subsInd6,subsInd8]
subsInd4=Inner[ReverseApplied[Rule],indPerm4,{x,a,b,c},List];
subsInd6=Inner[ReverseApplied[Rule],indPerm6,{x,a,b,c,d,e},List];
subsInd8=Inner[ReverseApplied[Rule],indPerm8,{x,a,b,c,d,e,f,g},List];


(* ::Subsubsection::Closed:: *)
(*Translate basis*)


Clear[toSmallUBasis]
toSmallUBasis[terms_]:=Module[
{f1,f2, SEQ, COM, ACOM,Du, subsChit, changeNotationDer, derToSmallU,chiralOfX, 
subFieldsWithoutDer, cleanTracesFull,aux,rmEvenIP,tagIP},

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

(*REMOVE EVEN INTRINSIC PARITY TERMS*)
rmEvenIP[expr_]:=(expr//onTermsStrict[tagIP])/.{evenIP->0,oddIP->1};
tagIP[term_]:= If[EvenQ@nFields[term,u|fm|chim],evenIP,oddIP]*term;
aux=aux//rmEvenIP; (*In the end it was not needed*)

aux
]


Clear[changeNotationContact]
changeNotationContact[finalbasis_]:=finalbasis/.TR[DD[FL,n_][ind__]]:>(1/2)*TR[DD[FL,n][ind]+DD[FR,n][ind]]/.TR[DD[FR,n_][ind__]]:>(1/2)*TR[DD[FL,n][ind]+DD[FR,n][ind]]//factorContact;

Clear[factorContact]
factorContact[list_]:=Map[If[!FreeQ[#,FL|FR|chi|chit|chid|chitd],Factor[#], Identity[#]]&,list];



(* ::Subsection::Closed:: *)
(*Options*)


ORDER=6;
zeroTrF=True;

(*import["P8"]*)


(* ::Text:: *)
(*[The [import] tag indicates the (3) cells that must be executed if importing previous data. These cells are also part of the normal calculation flow]*)


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


(* ::Subsubsection::Closed:: *)
(*Get the initial overcomplete basis*)


(* ::Text:: *)
(*Reduce the list of possibleTerms accounting for obvious zeroes, permutations of indices and cyclicity of traces. We do this in two alternative ways*)
(**)
(*1. Simpler method: (1) remove easy zeroes following from definitions;  (2) ignore Levi-Civita 'm'  index permutations (can only give signs), generate all possible shapes of each term, sort them, save first shape of each term, delete duplicates, reintroduce epsilon indices; (3) (use a more involved function to) remove terms that are both symmetric and antisymmetric on some index permutation. This leads to 402 (31568) different possible terms in p^6 (p^8)*)


possibleTerms//removeEasyZeroes//DeleteCases[0]//showLength;
lagWithZeroes=%//ignoreM//Map[generateAlternativeShapesNoEps]//Map[Sort]//Map[First]//DeleteDuplicates//reintroduceM//showTiming//showLength;
lag=%//removeSymAntisymZeroes//DeleteCases[0]//showTiming//showLength;


(* ::Text:: *)
(*2. More involved method: in step (2), rewrite each term into a standard shape, but not by generating all shapes first and comparing, but by defining a canonical order for relative position of indices, fields inside traces, relative position of two traces, etc. Defining this standard way of writing the terms is no easy task and one has to break all possible ambiguities by hand (symmetry of indices, repeated elements in traces, ...). I kept this method here for comparison (and a little bit out of emotional attachment). It is also slightly faster, even accounting for Levi-Civita indices.*)


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


ruleFMU1=DD[u,n_?(#==1&)][ind___,a_,b_]:>DD[u,n][ind,a,b] - DD[u,n][ind,b,a]+DD[fm,n-1][ind,a,b];
ruleFMU2=DD[fm,n_?(#==0&)][ind___,a_,b_]:>DD[u,n+1][ind,a,b] - DD[u,n+1][ind,b,a]+DD[fm,n][ind,a,b];

checkRule[ruleFMU1];
checkRule[ruleFMU2];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules and get the operator relations*)


lagFMU1=lag//findWithMinNDer[u,1]//showLength;
lagFMU2=lag//findWithMinNDer[fm,0]//showLength;

fullFMU1=getRelationsFromRule[lagFMU1,ruleFMU1]//showTiming;
fullFMU2=getRelationsFromRule[lagFMU2,ruleFMU2]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullFMU1,fullFMU2]//reshapeTerms//showTiming;
relFMU=%//identifyTerms//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[EOM] Equations of motion*)


(* ::Text:: *)
(*Define the identities*)


ruleEOM1=DD[u,n_?(#==1&)][ind___,a_,a_]:>DD[u,n][ind,a,a] -(1/2)ii DD[chim,n-1][ind]+TR[(1/2)(1/Nf)ii DD[chim,n-1][ind]];
ruleEOM2=DD[chim,n_?(#==0&)][ind___]:>DD[u,n+1][ind,j2,j2] -(1/2)ii DD[chim,n][ind]+TR[(1/2)(1/Nf)ii DD[chim,n][ind]];

checkRule[ruleEOM1];
checkRule[ruleEOM2];


(* ::Text:: *)
(*Get the operator relations*)


fullEOM1=getRelationsFromRule[lag,ruleEOM1]//onTermsStrict[assesJPair]//showTiming;
fullEOM2=getRelationsFromRule[lag,ruleEOM2]//onTermsStrict[assesJPair]//showTiming;


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


ruleBIm1=DD[fm,1][a_,b_,c_]:>DD[fm,1][a,b,c] +DD[fm,1][b,c,a]+DD[fm,1][c,a,b]+
(ii/2)(seq[DD[u,0][a] ,DD[fp,0][b,c]] + 
seq[DD[u,0][b] ,DD[fp,0][c,a]] +
seq[DD[u,0][c] ,DD[fp,0][a,b]])-
(ii/2)(seq[DD[fp,0][b,c],DD[u,0][a] ] +
 seq[DD[fp,0][c,a],DD[u,0][b] ] +
seq[DD[fp,0][a,b],DD[u,0][c]]);

Clear[a,b,c,A,B]

ruleBIm2a=TR[A___,DD[u,0][a_],DD[fp,0][b_,c_],B___]->TR[A,ruleBIm1[[2]],B];
ruleBIm2b=TR[DD[fp,0][b_,c_],A__,DD[u,0][a_]]->TR[ruleBIm1[[2]],A];

ruleBIm3a=TR[A___,DD[fp,0][b_,c_],DD[u,0][a_],B___]->TR[A,ruleBIm1[[2]],B];
ruleBIm3b=TR[DD[u,0][a_],A__,DD[fp,0][b_,c_]]->TR[ruleBIm1[[2]],A];


checkRule[ruleBIm1];
checkRule[ruleBIm2a];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules*)


lagBI1=Select[lag,Count[#,DD[(fm|fp),n_?(#>0&)][ind___],99]>0&]//showLength;
lagBI2=Select[lag,Count[#,TR[___,DD[u,0][__],DD[(fm|fp),0][__],___]|TR[DD[(fm|fp),0][__],___,DD[u,0][__]],99]>0&]//showLength;
lagBI3=Select[lag,Count[#,TR[___,DD[(fm|fp),0][__],DD[u,0][__],___]|TR[DD[u,0][__],___,DD[(fm|fp),0][__]],99]>0&]//showLength;


(* ::Text:: *)
(*Get the operator relations*)


fullBIm1=getRelationsFromRule[lagBI1,ruleBIm1]//showTiming;
fullBIm2a=getRelationsFromRule[lagBI2,ruleBIm2a]//showTiming;
fullBIm2b=getRelationsFromRule[lagBI2,ruleBIm2b]//showTiming;
fullBIm3a=getRelationsFromRule[lagBI3,ruleBIm3a]//showTiming;
fullBIm3b=getRelationsFromRule[lagBI3,ruleBIm3b]//showTiming;


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


checkRule[ruleBIp1];
checkRule[ruleBIp2a];


(* ::Text:: *)
(*Get the operator relations*)


fullBIp1=getRelationsFromRule[lagBI1,ruleBIp1]//showTiming;
fullBIp2a=getRelationsFromRule[lagBI2,ruleBIp2a]//showTiming;
fullBIp2b=getRelationsFromRule[lagBI2,ruleBIp2b]//showTiming;
fullBIp3a=getRelationsFromRule[lagBI3,ruleBIp3a]//showTiming;
fullBIp3b=getRelationsFromRule[lagBI3,ruleBIp3b]//showTiming;


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
fullSCH=lagSCH//Map[getSchouten4m]//Flatten//DeleteDuplicates//showTiming//showLength;


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

ruleCOM1=DD[X_,n_?(#>=2&)][a_,b_,ind___]:>
-DD[X,n][a,b,ind] +DD[X,n][b,a,ind]  +
(1/4)*(
seq[DD[u,0][a],DD[u,0][b],DD[X,n-2][ind]] -
 seq[DD[u,0][b],DD[u,0][a],DD[X,n-2][ind]]) -( ii/2) seq[DD[fp,0][a,b],DD[X,n-2][ind]]- 
(1/4)*(
seq[DD[X,n-2][ind],DD[u,0][a],DD[u,0][b]] - 
seq[DD[X,n-2][ind],DD[u,0][b],DD[u,0][a]]) + ( ii/2) seq[DD[X,n-2][ind],DD[fp,0][a,b]];

ruleCOM2a=TR[DD[u,0][a_],DD[u,0][b_],DD[X_,n_][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
ruleCOM3a=TR[DD[fp,0][a_,b_],DD[X_,n_][ind___],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];

(*Not necesary 2b and 3b: 9331 rel anyway*)
ruleCOM2b=TR[DD[X_,n_][ind___],DD[u,0][a_],DD[u,0][b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];
ruleCOM3b=TR[DD[X_,n_][ind___],DD[fp,0][a_,b_],A___]->TR[(ruleCOM1[[2]]/.n->n+2),A];

checkRule[ruleCOM1];
(*In this case the other rules can't be checked. See ?checkRule*)


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


fullCOM1=getRelationsFromRule[lagCOM1,ruleCOM1]//showLength//showTiming;
fullCOM2a=getRelationsFromRule[lagCOM2,ruleCOM2a]//showLength//showTiming;
fullCOM3a=getRelationsFromRule[lagCOM3,ruleCOM3a]//showLength//showTiming;
fullCOM2b=getRelationsFromRule[lagCOM2,ruleCOM2b]//showLength//showTiming;
fullCOM3b=getRelationsFromRule[lagCOM3,ruleCOM3b]//showLength//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullCOM1,fullCOM2a,fullCOM3a,fullCOM2b,fullCOM3b]//reshapeTerms//showTiming;
relCOM=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[CH] Cayley-Hamilton (nf=2,3)*)


(* ::Text:: *)
(*Get the operator relations*)


fullCH[2]=lag//getCayleyHamilton[2]//showTiming;
fullCH[3]=lag//getCayleyHamilton[3]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


relCH[2]=fullCH[2]//reshapeTerms//identifyTerms//deleteDuplicatesSign//showLength//showTiming;
relCH[3]=fullCH[3]//reshapeTerms//identifyTerms//deleteDuplicatesSign//showLength//showTiming;


(* ::Text:: *)
(*We ignore higher Nf cases to speed up, but they can be obtained  just in the same way*)


Do[relCH[i]={},{i,4,100}]


(* ::Subsection::Closed:: *)
(*Reorder operators*)


(* ::Subsubsection::Closed:: *)
(*Symmetrize on H and C*)


(* ::Text:: *)
(*Define discrete transformations.*)
(*Find linear combinations of terms that are even under H and eigenvectors of C.*)
(*Define transformation from the symmetric to the raw operator basis. *)


Clear[applyC,applyH]
applyC[terms_]:=(terms/.DD[fp,n_][i___]:>sign DD[fp,n][i])//reverseTR//pullSign//reshapeTermsBare
applyH[terms_]:=(terms/.DD[chim,n_][i___]:>sign DD[chim,n][i]//simpleConjugate)//reverseTR//pullSign//reshapeTermsBare

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
hasNotHas[term,fm|fp,chim|chip]                * 10^-2 + 
hasField[term,fm|fp]*hasField[term,chim|chip] * 10^-3 + (*irrelevant*)
nTraces[term]                   * 10^-4 +
(10 - nFields[term,chim|chip])  * 10^-6 +
(10 - nFields[term,fm|fp])      * 10^-7 +
(10 - nFields[term,u])          * 10^-8 +
nDer[term]               * 10^-9 +
nSeqDer[term]            * 10^-10


(*lag[[1;;-1;;100]];
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


(* ::Text:: *)
(*Execute the symmetry definitions (copied from above)*)


(*REDEFINING... CAUTION!!*)

Clear[applyC,applyH]
applyC[terms_]:=(terms/.DD[fp,n_][i___]:>sign DD[fp,n][i])//reverseTR//pullSign//reshapeTermsBare
applyH[terms_]:=(terms/.DD[chim,n_][i___]:>sign DD[chim,n][i]//simpleConjugate)//reverseTR//pullSign//reshapeTermsBare


(* ::Subsection::Closed:: *)
(*Reduce to minimal basis*)


(* ::Text:: *)
(*Now we put together all the previous results of the calculation to do the reduction to a minimal basis.*)
(*First we transform the relations (in the raw basis) into the proper orderings (pref basis). Optionally, remove C odd operators to speed up. And build a relation matrix with the operator relations. *)
(*Gaussian Elimination is performed. In particular the relation matrix is decomposed into a unitary (Q) and an upper triangular (R)  matrix with getMinimalBasis, which uses the third-party code SuiteSparseQR, written in C++.*)
(*The transformations are undone to be able to read the terms of the final basis.*)
(**)


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->8;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisGenNf = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->3;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisGenNf3 = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;


{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->2;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasis = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

miniBasisGenNf2 = summary[miniBasis, {Identity}, 
(chip | chim):>0, 
(fp | fm):>0 ,
(chip | chim | fp | fm):>0
] ;


(* ::Subsection::Closed:: *)
(*Time*)


Now-START


(* ::Subsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/P8DUMMY.mx",
{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH,
lag, lagShapes, lagShapesZeroes, opesCE, opesCO,
rawToSymOpes, symToPrefOpes, prefToSymOpes, symToRawOpes, rawOpesToTerms,
miniBasisGenNf3,miniBasisGenNf2,miniBasisGenNf
}];


(* ::Subsection::Closed:: *)
(*Remove contact terms from full basis*)


(* ::Subsubsection::Closed:: *)
(*Mixed notation*)


Clear[cal]
cal[expr_]:=expr/.
{fm:>SuperMinus[\[ScriptF]],fp:>SuperPlus[\[ScriptF]],chim:>SuperMinus[\[Chi]],chip:>SuperPlus[\[Chi]],u:>\[ScriptU]}/.
{FL:>F^L,FR:>F^R,chi-> \[Chi],chid-> SuperDagger[\[Chi]],chit-> \!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\),chitd-> SuperDagger[\!\(\*OverscriptBox[\(\[Chi]\), \(~\)]\)],U->U,Ud-> SuperDagger[U]}


(* ::Subsubsection::Closed:: *)
(*Reobtain minimal basis with contact terms*)


(* ::Text:: *)
(*Check bases*)


import["P8contactBasisNf2"]
{Range[Length[contactTerms]],contactTerms,contactTerms//toSmallUBasis//reshapeTermsBare}//Transpose//see;


(* ::Text:: *)
(*Redo Gaussian elimination*)


import["P8contactBasisNf2"]

{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->2; 
rel = % // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF];

contactOpe = rel//additionalOpesFor[contactTerms];
contactOpeToTerms = #/.MapThread[Rule,{contactOpe,contactTerms}] &;
contactRelations= contactTerms//toSmallUBasis//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF//contactOpe - # &;

extendedRelationMatrix = rel //Append[contactRelations] //getRelationMatrix//EchoFunction[MatrixPlot];

miniBasisWithContactNf2 = extendedRelationMatrix // getMinimalBasis //showTiming //contactOpeToTerms// prefToSymOpesF// symToRawOpesF // rawOpesToTerms // rmOverallReal // changeNotationContact ;

basesDiff[miniBasisWithContactNf2,miniBasisGenNf2]


(* ::Text:: *)
(*CAUTION! For TRF = 0, no contact terms: just:*)


(*miniBasisWithContactNf = miniBasisGenNf;
miniBasisWithContactNf3 = miniBasisGenNf3;*)


(* ::Text:: *)
(*For TRF != 0 :*)


import["P8TRFcontactBasisNf3"]

{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->3; 
rel = % // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF];

contactOpe = rel//additionalOpesFor[contactTerms];
contactOpeToTerms = #/.MapThread[Rule,{contactOpe,contactTerms}] &;
contactRelations= contactTerms//toSmallUBasis//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF//contactOpe - # &;

extendedRelationMatrix = rel //Append[contactRelations] //getRelationMatrix//EchoFunction[MatrixPlot];

miniBasisWithContactNf3 = extendedRelationMatrix // getMinimalBasis //showTiming //contactOpeToTerms// prefToSymOpesF// symToRawOpesF // rawOpesToTerms // rmOverallReal // changeNotationContact ;

basesDiff[miniBasisWithContactNf3,miniBasisGenNf3]


import["P8TRFcontactBasisNf"]

{relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->8; 
rel = % // rawToSymOpesF // symToPrefOpesF //remove[opesCO//symToPrefOpesF];

contactOpe = rel//additionalOpesFor[contactTerms];
contactOpeToTerms = #/.MapThread[Rule,{contactOpe,contactTerms}] &;
contactRelations= contactTerms//toSmallUBasis//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF//contactOpe - # &;

extendedRelationMatrix = rel //Append[contactRelations] //getRelationMatrix//EchoFunction[MatrixPlot];

miniBasisWithContactNf = extendedRelationMatrix // getMinimalBasis //showTiming //contactOpeToTerms// prefToSymOpesF// symToRawOpesF // rawOpesToTerms // rmOverallReal // changeNotationContact ;

basesDiff[miniBasisWithContactNf,miniBasisGenNf]


(* ::Subsubsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/P8basisDUMMY.mx",
{
miniBasisGenNf,miniBasisGenNf2,miniBasisGenNf3,
miniBasisWithContactNf,miniBasisWithContactNf2,miniBasisWithContactNf3
}];


(* ::Subsection::Closed:: *)
(*Test equivalence bases*)


(* ::Text:: *)
(*Check Hermiticity and C conjugation*)


import["finalbasesHans/basishansTRACEnf3"]
basis//reshapeTermsBare//showLength;

%//signsUnder[applyH]//Tally


(* ::Text:: *)
(*Test equivalence*)


NF=6;
import["finalbasesHans/basishansNOTRACEnf6"]
bHans=basis//removeTermsWith[fp|fm]//showLength;
bJoan=miniBasisGenNf//removeTermsWith[fp|fm]//showLength;

bHans=bHans//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF;
bJoan=bJoan//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF;
rel={relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->NF  // rawToSymOpesF//symToPrefOpesF//remove[opesCO//symToPrefOpesF]//showLengthFlat;

testEquivalenceBases[bHans,bJoan,rel]//showTiming


(* ::Text:: *)
(*Test if a basis has redundant operators*)


NF=2;
import["finalbasesHans/basishansTRACEnf2"]
bHans=basis//removeTermsWith[chip|chim]//reshapeTerms//symmetrize[applyH,applyC]//identifyTerms//rawToSymOpesF//symToPrefOpesF;
rel={relTD,relBIp,relEOM,relFMU,relCOM,relSCH,relCH[Nf]} /. Nf->NF  // rawToSymOpesF//symToPrefOpesF//remove[opesCO//symToPrefOpesF]//showLengthFlat;

bHans//getRedundantOperatorsUsing[rel] // toOpeTagsIn[bHans]
