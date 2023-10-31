(* ::Package:: *)

Quit[]


AppendTo[$Path, ParentDirectory[NotebookDirectory[]]];
Needs["MINIBAR`"]


(* ::Chapter:: *)
(*ChPT: anomalous sector. LR basis. Contact terms. Order p^6-p^8*)


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


(* ::Subsubsection::Closed:: *)
(*Reduce to minimal basis*)


Clear[changeNotationContact]
changeNotationContact[finalbasis_]:=finalbasis/.TR[DD[FL,n_][ind__]]:>(1/2)*TR[DD[FL,n][ind]+DD[FR,n][ind]]/.TR[DD[FR,n_][ind__]]:>(1/2)*TR[DD[FL,n][ind]+DD[FR,n][ind]]//Factor;


(* ::Text:: *)
(*Apply tr(fm)=0. In this base it takes the shape tr(FL)=tr(FR)*)


(*DEPRECATED: now it is an operator relation*)
Clear[makeEqualtrFLR]
makeEqualtrFLR[expr_]:=Module[{aux,makeFLtoFR},
makeFLtoFR=(#/.TR[DD[FL,n_][ind___]]:>TR[DD[FR,n][ind]]//reshapeTermsBare) &;

aux=expr;
aux=aux//deleteZeroesBy[makeFLtoFR];
aux=aux//deleteDuplicatesSignBy[makeFLtoFR]
]


(* ::Subsection::Closed:: *)
(*Options*)


ORDER=8;
zeroTrF=False;
NF=2;
maxU=0;

(*import["P8TRFcontactNf2"]*)


(* ::Text:: *)
(*[The [import] tag indicates the (3) cells that must be executed if importing previous data. These cells are also part of the normal calculation flow]*)


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


(* ::Subsubsection::Closed:: *)
(*Get the initial overcomplete basis*)


(* ::Text:: *)
(*Reduce the list of possibleTerms accounting for obvious zeroes.*)
(*Then generate all ways of writing the terms to find duplicates (ignoring signs).*)
(*Then remove vanishing terms due to symmetric x antisymmetric indices.*)


possibleTerms//removeEasyZeroes//keepChiralInvariant//DeleteCases[0]//showLength;
lagWithZeroes = %//Map[generateAlternativeShapesUnsigned]//Map[Sort]//Map[First]//DeleteDuplicates//showTiming//showLength;
lagRandomShapes = %//Map[generateAlternativeShapesSigned]//Map[DeleteDuplicates]//ignoreSigns//Select[DuplicateFreeQ]//Map[First]//showTiming//showLength;


(* ::Subsubsection::Closed:: *)
(*Alternative shapes [Import]*)


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


(* ::Subsubsection::Closed:: *)
(*Identify terms [Import]*)


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


ruleBIFL=DD[FL,1][a_,b_,c_]:>DD[FL,1][a,b,c] +DD[FL,1][b,c,a]+DD[FL,1][c,a,b];
ruleBIFR=DD[FR,1][a_,b_,c_]:>DD[FR,1][a,b,c] +DD[FR,1][b,c,a]+DD[FR,1][c,a,b];

checkRule[ruleBIFL];
checkRule[ruleBIFR];


(* ::Text:: *)
(*Preselect candidate terms to insert the rules*)


lagBI=lag//find[FL|FR];


(* ::Text:: *)
(*Get the operator relations*)


fullBIFL=getRelationsFromRule[lagBI,ruleBIFL]//showTiming;
fullBIFR=getRelationsFromRule[lagBI,ruleBIFR]//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


Join[fullBIFR,fullBIFL]//reshapeTerms//showTiming;
relBI=%//identifyTerms//deleteDuplicatesSign//showLength;


relBI//Map[removeOverallFactor]//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[COM] Commutation of derivatives*)


(* ::Text:: *)
(*Define the identities*)


Clear[a,b,c,A,B]


Clear[chiralFMatricesOf]
chiralFMatricesOf[X]:={FXL,FXR}
chiralFMatricesOf[X_]:= chiralTransform[TR[DD[X,0][]]]/.TR[T1_,aa_,T2_]:>{T1,T2}/.{L->FL,R->FR}
(*chiralFMatricesOf[chi]*)

ruleCOM=DD[X_,n_?(#>=2&)][a_,b_,ind___]:>(
{F1,F2}=chiralFMatricesOf[X];
DD[X,n][a,b,ind] -
DD[X,n][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n-2][ind]]-
ii*seq[DD[X,n-2][ind],DD[F2,0][a,b]]);

checkRule[ruleCOM]


ruleCOM2=TR[DD[F:(FR|FL),0][a_,b_],DD[X_,n_?(#>=0&)][ind___],A___]:>(
{F1,F2}=chiralFMatricesOf[X];
TR[(DD[X,n+2][a,b,ind] -
DD[X,n+2][b,a,ind]  + 
ii*seq[DD[F1,0][a,b],DD[X,n][ind]]-
ii*seq[DD[X,n][ind],DD[F2,0][a,b]]),A]);



ruleCOM3=TR[DD[X_,n_?(#>=0&)][ind___],DD[F:(FR|FL),0][a_,b_],A___]:>(
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


fullCOM1=getRelationsFromRule[lagCOM,ruleCOM]//showLength//showTiming;
fullCOM2=getRelationsFromRule[lagCOMall,ruleCOM2]//showLength//showTiming;
fullCOM3=getRelationsFromRule[lagCOMall,ruleCOM3]//showLength//showTiming;


Join[fullCOM1,fullCOM2,fullCOM3]//reshapeTerms//showTiming//showLength;
relCOM=%//identifyTerms//deleteDuplicatesSign//showLength;


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
fullSCH=lagSCH//Map[getSchouten4m]//Flatten//DeleteDuplicates//showTiming//showLength;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullSCH//reshapeTerms//showTiming;
relSCH=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[CH] Cayley-Hamilton (nf=2,3)*)


(* ::Text:: *)
(*In this case, the chiral transformation is not trivial as in the small-u parametrization. Thus the wrapper getCayleyHamilton is not employed here. This allows to check the chiral invariance in an intermediate step.*)


(* ::Text:: *)
(*Expand the terms such that the traces appear in any possible order (rotateTraces). *)
(*Then surround the first 2 (3) matrices, for nf = 2 (3), with a List. The CH relation will be applied on those groups.*)


lagCH=lag//rotateTraces//showLength;

lagGroupedNf2=(lagCH//separateArgsTR[2])//Flatten//showTiming//showLength;
lagGroupedNf2=%//sortGroupsCH//DeleteDuplicates//showLength;
lagGroupedNf2=%//chiralTransform//keepUnmixedLRGroups//DeleteCases[0]//showLength;

lagGroupedNf3=(lagCH//separateArgsTR[3])//Flatten//showTiming//DeleteDuplicates//showLength;
lagGroupedNf3=%//sortGroupsCH//DeleteDuplicates//showLength;
lagGroupedNf3=%//chiralTransform//keepUnmixedLRGroups//DeleteCases[0]//showLength;



(* ::Text:: *)
(*Define the CH trace identities for nf=2,3*)


ruleCHNf2=getRuleCayleyHamilton[2];
ruleCHNf3=getRuleCayleyHamilton[3];

checkRule[ruleCHNf2];
checkRule[ruleCHNf3];


(*ruleCHNf2=TR[{B__},{C__},Z___]:>TR[B,C,Z]+TR[C,B,Z]-TR[B,TR[C],Z]-TR[C,TR[B],Z]-TR[TR[B,C],Z]+TR[TR[B],TR[C],Z];

ruleCHNf3=TR[{B__},{C__},{D__},Z___]:>
TR[B,C,D,Z]+TR[D,B,C,Z]+TR[C,B,D,Z]+TR[D,C,B,Z]+TR[C,D,B,Z]+TR[B,D,C,Z]-TR[D,B,TR[C],Z]-
TR[B,D,TR[C],Z]-TR[B,C,TR[D],Z]-TR[C,B,TR[D],Z]-TR[D,C,TR[B],Z]-TR[C,D,TR[B],Z]-TR[D,TR[B,C],Z]-
TR[B,TR[C,D],Z]-TR[C,TR[B,D],Z]-TR[TR[B,C,D],Z]-TR[TR[C,B,D],Z]+TR[D,TR[B],TR[C],Z]+TR[B,TR[C],TR[D],Z]+
TR[C,TR[B],TR[D],Z]+TR[TR[D],TR[B,C],Z]+TR[TR[B],TR[C,D],Z]+TR[TR[C],TR[B,D],Z]-TR[TR[B],TR[C],TR[D],Z];

checkRule[ruleCHNf2];
checkRule[ruleCHNf3];*)


(* ::Text:: *)
(*Get operator relations*)


fullCHNf2=getRelationsFromRule[ lagGroupedNf2,ruleCHNf2]/.Nf->2//showTiming;
fullCHNf3=getRelationsFromRule[ lagGroupedNf3,ruleCHNf3]/.Nf->3//showTiming;


(* ::Text:: *)
(*Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullCHNf2//reshapeTerms//showTiming;
relCH[2]=%//identifyTerms//deleteDuplicatesSign//showLength;


fullCHNf3//reshapeTerms//showTiming;
relCH[3]=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Text:: *)
(*We ignore CH relations for higher Nf, but they can be obtained all the same *)


Do[relCH[i]={},{i,4,100}]


(* ::Subsubsection::Closed:: *)
(*[FLR] tr(FR) = tr(FL)*)


(* ::Text:: *)
(*Define the identities*)


ruleFLR=TR[DD[FL,n_?(#>=0&)][ind__]]:>TR[DD[FR,n][ind]] - TR[DD[FL,n][ind]] ;
checkRule[ruleFLR];


(* ::Text:: *)
(*Get the operator relations. Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


fullFLR=getRelationsFromRule[lag,ruleFLR]//showTiming;
fullFLR//reshapeTerms//showTiming;
relFLR=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsubsection::Closed:: *)
(*[CHIT]*)


(* ::Text:: *)
(*Define the identities*)


ruleCHIT1=TR[A__,DD[chi,0][],DD[chitd,0][]]:>(1/NF)*TR[A]TR[DD[chi,0][],DD[chitd,0][]] - TR[A,DD[chi,0][],DD[chitd,0][]] ;
ruleCHIT2=TR[A__,DD[chid,0][],DD[chit,0][]]:>(1/NF)*TR[A]TR[DD[chid,0][],DD[chit,0][]] - TR[A,DD[chid,0][],DD[chit,0][]] ;
ruleCHIT3=TR[A__,DD[chit,0][],DD[chid,0][]]:>(1/NF)*TR[A]TR[DD[chit,0][],DD[chid,0][]] - TR[A,DD[chit,0][],DD[chid,0][]] ;
ruleCHIT4=TR[A__,DD[chitd,0][],DD[chi,0][]]:>(1/NF)*TR[A]TR[DD[chitd,0][],DD[chi,0][]] - TR[A,DD[chitd,0][],DD[chi,0][]] ;

checkRule[ruleCHIT1];
checkRule[ruleCHIT2];
checkRule[ruleCHIT3];
checkRule[ruleCHIT4];


(* ::Text:: *)
(*Get the operator relations. Standardize shapes of the terms, remove zeroes, and identify the terms with the 'lag' basis. *)


lagRot=rotateTraces[lag];


fullCHIT={
getRelationsFromRule[lagRot,ruleCHIT1],
getRelationsFromRule[lagRot,ruleCHIT2],
getRelationsFromRule[lagRot,ruleCHIT3],
getRelationsFromRule[lagRot,ruleCHIT4]
}//Flatten//showTiming;

fullCHIT//reshapeTerms//showTiming;
relCHIT=%//identifyTerms//deleteDuplicatesSign//showLength;


(* ::Subsection::Closed:: *)
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
applyH[terms_]:=(terms/.{chi:>chid,chit:>chitd,chid:>chi,chitd:>chit}//simpleConjugate)//reverseTR//pullSign//reshapeTermsBare//addSigns

test=lag//showLength//symmetrize[applyH,applyP,applyC]//showTiming//showLength;
symToRawOpes=%//identifyTerms//getTransformationRules//showTiming//showLength;
{opesPCE,opesPCO}=separateEvenOddUnder[applyC,applyP][symToRawOpes,lag]//showTiming;


rawToSymOpes=symToRawOpes//getInverseTransformation//showTiming;


(* ::Subsubsection::Closed:: *)
(*Reorder and promote C even terms*)


(* ::Text:: *)
(*Define the preferential the terms for the final minimal basis.*)


Clear[scorePreferredOperators]
scorePreferredOperators = Identity


Clear[scorePreferredOperators]
scorePreferredOperators[term_]:=
nFields[term,DD[chit|chitd,_][__]]                                   * 100 +
hasField[term,chit|chitd]*hasField[term,chi|chid]*(10-nTraces[term]) * 10 + (*Retains TR[chitd,chi]TR[FL] rather than TR[chitd,chi,FL]*)
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
{%,%//Map[scorePreferredOperators]//N//Map[FullForm]}//Transpose//see;*)

(*(ope/@Range[402])/.prefToSymOpes/.ope[i_]\[RuleDelayed]lag[[i]]//Reverse;*)


(* ::Subsection::Closed:: *)
(*Reduce to minimal basis*)


(* ::Text:: *)
(*Now we put together all the previous results of the calculation to do the reduction to a minimal basis, based on the relations we found.*)
(*First we transform the relations (in the raw basis) into the proper orderings (pref basis). Optionally, remove C odd operators beforehand to speed up. And build a relation matrix with the operator relations. *)
(*Gaussian Elimination is performed. In particular the relation matrix is decomposed into a unitary (Q) and an upper triangular (R)  matrix with getMinimalBasis, which uses the third-party code SuiteSparseQR, written in C++.*)
(*The transformations are undone to be able to read the terms of the final basis.*)
(**)


{relTD,relBI,relCOM,relSCH,relCH[Nf],relFLR,relCHIT} /. Nf->NF;
relationMatrix = %  // rawToSymOpesF // symToPrefOpesF //remove[opesPCO//symToPrefOpesF] // getRelationMatrix // showTiming;
relationMatrix // MatrixPlot
miniBasisEvenNf2 = relationMatrix // getMinimalBasis //showTiming // prefToSymOpesF// symToRawOpesF // rawOpesToTerms;

summary[%, {applyC,applyP}, 
1:>1
] ;


(* ::Subsection::Closed:: *)
(*Save results*)


DumpSave[NotebookDirectory[]<>"/save/P8TRFcontactNf2DUMMY.mx",
{relTD,relBI,relCOM,relSCH,relCH,relFLR,relCHIT,
lag, lagWithZeroes,lagRandomShapes, opesPCE, opesPCO,
rawToSymOpes, symToPrefOpes, prefToSymOpes, symToRawOpes, rawOpesToTerms,
miniBasisEvenNf2
}];



contactTerms=miniBasisEvenNf2;
DumpSave[NotebookDirectory[]<>"/save/P8TRFcontactBasisNf2DUMMY.mx",
{
contactTerms
}];


(* ::Subsection::Closed:: *)
(*Time*)


Now-START


(* ::Subsection::Closed:: *)
(*Check equivalence of contact operator bases*)


contactTerms=miniBasisEvenNf2;
contactTermsHans={TR[DD[FL,1][m3,j1,m4]] TR[DD[FL,0][j1,m2],DD[FL,1][j2,j2,m1]]-TR[DD[FR,1][m3,j1,m4]] TR[DD[FR,0][j1,m2],DD[FR,1][j2,j2,m1]],TR[DD[FL,0][j2,m4]] TR[DD[FL,1][j2,j1,m1],DD[FL,1][m2,j1,m3]]-TR[DD[FR,0][j2,m4]] TR[DD[FR,1][j2,j1,m1],DD[FR,1][m2,j1,m3]],I TR[DD[FR,0][m3,m4]] TR[DD[chi,0][],DD[chitd,0][],DD[FR,0][m1,m2]]+I TR[DD[FL,0][m3,m4]] TR[DD[chi,0][],DD[FL,0][m1,m2],DD[chitd,0][]]-I TR[DD[FL,0][m3,m4]] TR[DD[chid,0][],DD[chit,0][],DD[FL,0][m1,m2]]-I TR[DD[FR,0][m3,m4]] TR[DD[chid,0][],DD[FR,0][m1,m2],DD[chit,0][]],I TR[DD[chi,0][],DD[chitd,0][],DD[FR,0][m1,m2],DD[FR,0][m3,m4]]+I TR[DD[chi,0][],DD[FL,0][m1,m2],DD[FL,0][m3,m4],DD[chitd,0][]]-I TR[DD[chid,0][],DD[chit,0][],DD[FL,0][m1,m2],DD[FL,0][m3,m4]]-I TR[DD[chid,0][],DD[FR,0][m1,m2],DD[FR,0][m3,m4],DD[chit,0][]],I TR[DD[chi,0][],DD[FL,0][m1,m2],DD[chitd,0][],DD[FR,0][m3,m4]]-I TR[DD[chid,0][],DD[FR,0][m1,m2],DD[chit,0][],DD[FL,0][m3,m4]]};


contactTerms//reshapeTerms//changeNotationContact//rmOverallReal//changeNotationContact//see;
contactTermsHans//reshapeTerms//see;


(* ::Text:: *)
(*CHECK EQUIVALENCE CONTACT TERM BASES*)


b1=contactTerms//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF;
b2=contactTermsHans//reshapeTerms//identifyTerms//rawToSymOpesF//symToPrefOpesF;

rel={relTD,relBI,relCOM,relSCH,relCH[Nf],relFLR,relCHIT} /. Nf->2  // rawToSymOpesF//symToPrefOpesF//remove[opesPCO//symToPrefOpesF]//showLengthFlat;

testEquivalenceBases[b1[[1;;2]],b2[[4;;5]],rel]
