(* ::Package:: *)

(* ::Title:: *)
(*FindClosedForm (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["FindClosedForm`"];


FindClosedForm::usage=
"FindClosedForm[y]
  searches for equivalents to the given number y from common mathematical functions.

FindClosedForm[y, n]
  returns up to n results for the number y.

FindClosedForm[y, f]
  searches for a formula with the given functional form f.

FindClosedForm[y, f, n]
  returns up to n results.

FindClosedForm[y, {f1, f2, \[Ellipsis]}]
  searches for a formula for the given number y, among the given list of functional forms fi.

FindClosedForm[y, {f1, f2, \[Ellipsis]}, n]
  returns up to n results.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection:: *)
(*Auxiliary functions*)


(* ::Subsubsection::Closed:: *)
(*Argument search range*)


(* ::Text:: *)
(*The following function computes the argument range for each search round. It is set by default to the Farey range, which is made of rationals of uniform complexity.*)


(* ::Input::Initialization:: *)
(*the parameter cut is the search round number or also an upper integer cutoff*)
ClearAll[rangeFull]
Options[rangeFull]={"ComplexArg"->False,"SearchRange"->"Farey"};
rangeFull[cut_Integer,options:OptionsPattern[rangeFull]]:=
	Which[OptionValue["SearchRange"]==="Farey",
		If[!OptionValue["ComplexArg"],
			ResourceFunction["FareyRange"][-cut,cut,cut],
			ResourceFunction["ComplexRange"][-cut-I cut,cut+I cut,{cut,cut},"FareyRange"->True]],
		OptionValue["SearchRange"]==="Plain",
		If[!OptionValue["ComplexArg"],
			Range[-cut,cut,1/cut],
			ResourceFunction["ComplexRange"][-cut-I cut,cut+I cut,{1/cut,1/cut}]],
		OptionValue["SearchRange"]==="Integer",
		If[!OptionValue["ComplexArg"],
			Range[-cut,cut],
			ResourceFunction["ComplexRange"][-cut-I cut,cut+I cut]],
		Head[OptionValue["SearchRange"]]===Function,
		OptionValue["SearchRange"][cut]]


(* ::Text:: *)
(*A function which restricts the argument search range, that is it selects a "chamber". This exploits properties for each known function, so to speed up the search when certain options are used (see below "AlgebraicFactor" and "AlgebraicAdd", related to the internal option "Operation").*)


(* ::Input::Initialization:: *)
ClearAll[functionChamber]
Options[functionChamber]={"ComplexArg"->False,"RealValued"->True,"Operation"->"Times"};
functionChamber[x_,opts:OptionsPattern[functionChamber]]:=
(*x is the variable or slot*)
Which[OptionValue["Operation"]=="Times"&&!OptionValue["ComplexArg"]&&OptionValue["RealValued"],
<|Sin[\[Pi] #]&->0<=x<=1/2,Cos[\[Pi] #]&->0<=x<=1/2,Tan[\[Pi] #]&->0<=x<=1/2,Cot[\[Pi] #]&->0<=x<=1/2,Sec[\[Pi] #]&->0<=x<=1/2,Csc[\[Pi] #]&->0<=x<=1/2,ArcSin[#]&->0<=x<=1,ArcCos[#]&->-1<=x<=1,ArcTan[#]&->0<=x,ArcCot[#]&->0<=x,ArcSec[#]&->True,ArcCsc[#]&->0<=x,Exp[#]&->True,Log[#]&->1<=x,Sinh[#]&->0<=x,Cosh[#]&->0<=x,Tanh[#]&->0<=x,Coth[#]&->0<=x,Sech[#]&->0<=x,Csch[#]&->0<=x,ArcSinh[#]&->0<=x,ArcCosh[#]&->1<=x,ArcTanh[#]&->0<=x<=1,ArcCoth[#]&->0<=x,ArcSech[#]&->0<=x<=1,ArcCsch[#]&->0<=x,Gamma[#]&->0<=x<=1,Erf[#]&->0<=x,InverseErf[#]&->0<=x<=1,EllipticK[#]&->True,EllipticE[#]&->x<=1,Zeta[#]&->True,ProductLog[#]&->-(1/E)<=x|> ,
OptionValue["Operation"]=="Plus"&&!OptionValue["ComplexArg"]&&OptionValue["RealValued"],
<|PolyGamma[#]&->0<=x<=1|>,
OptionValue["Operation"]=="None"&&!OptionValue["ComplexArg"]&&OptionValue["RealValued"],
<||>,
Or[OptionValue["ComplexArg"],!OptionValue["RealValued"]],
<||>]
functionChamber[x_,fun_Function,opts:OptionsPattern[functionChamber]]/;MemberQ[Keys@functionChamber[x,opts],fun]:=Lookup[functionChamber[x,opts],fun]
functionChamber[x_,fun_Function,opts:OptionsPattern[functionChamber]]:=True


(* ::Subsubsection::Closed:: *)
(*Function evaluation*)


(* ::Text:: *)
(*Since an essential parameter of main function is the functional form 'fun', the following are simple utility functions to deal with the slots in it:*)


(* ::Input::Initialization:: *)
slotNumber[fun_Function]:=
	Length@slotArgs[fun]
slotArgs[fun_Function]:=
	Union@Cases[fun,_Slot,Infinity]
slotReplace[fun_Function]:=
	Normal@AssociationThread[slotArgs[fun],Table[Slot[i],{i,slotNumber[fun]}]]


(* ::Text:: *)
(*This function is used to manage the sub-functions appearing in the functional form 'fun', to be used only to better select the argument chamber:*)


(* ::Input::Initialization:: *)
functionCatch[fun_Function]:=
	Module[{a,p,patt,repl},
		(*the following alternatives are imcomplete, but it does not matter 
		for the later use of functionCatch only in functionValues to select a chamber*)
		patt=a_[p:PatternSequence[___,_Slot..,___]..]|
			a_[p:PatternSequence[___,Times[___,_Slot]..,___]..]|
			a_[p:PatternSequence[___,Times[_Slot,___]..,___]..]|
			a_[p:PatternSequence[___,Times[___,_Slot,___]..,___]..]|
			a_[p:PatternSequence[___,Plus[___,_Slot]..,___]..]|
			a_[p:PatternSequence[___,Plus[_Slot,___]..,___]..]|
			a_[p:PatternSequence[___,Plus[___,_Slot,___]..,___]..];
		repl=ReplaceAll[fun,patt:>Hold@Function[a[p]]];
		Union@Cases[repl,h_Hold:>ReleaseHold[h],Infinity]]


(* ::Text:: *)
(*The following function computes the values of the functional form 'fun' over the argument range. The latter is determined by the parameters 'rg' and 'del', which are the full range for each round and the previous range combinations already computed and so to delete.*)


(* ::Input::Initialization:: *)
ClearAll[functionValues]
Options[functionValues]=Join[Options[functionChamber],{"SearchArguments"->Automatic,"OutputArguments"->False}];
functionValues[fun_Function,rg_List,del_List:{},opts:OptionsPattern[functionValues]]:=
	Block[{funs,chamb,sel,sln,scrg,outer,args,vals,lv},
	
	scrg=OptionValue["SearchArguments"];
	
	Which[

	scrg===Automatic&&!OptionValue["ComplexArg"]&&OptionValue["RealValued"],
	(*when these options hold, it is possible to restrict the argument chamber*)
	funs=functionCatch[fun];
	sel=Map[Hold@Evaluate@
		functionChamber[slotArgs[#],
						#/.slotReplace[#],
						Sequence@@FilterRules[{opts},Options[functionChamber]]]
			/.{s_Slot}:>s&,
			funs];
	chamb=Map[Select[rg,#/.slotReplace[#]]&,Function@@@sel];
	sln=Map[slotNumber,funs];
	outer=Flatten[MapThread[Table[#1,#2]&,{chamb,sln}],1];,
	
	scrg===Automatic&&Or[OptionValue["ComplexArg"],!OptionValue["RealValued"]],
	outer=Table[rg,slotNumber[fun]],	

	scrg=!=Automatic,
	outer=If[Head[scrg]===List,
			If[Depth[scrg]==2,{scrg},scrg],
			Lookup[scrg,slotArgs[fun]]]];
	
	lv=slotNumber[fun]-1;

	(*delete previously computed combinations:*)
	args=Complement[Flatten[Outer[{##}&,Sequence@@outer],lv],del];
	vals=Quiet[
			If[!OptionValue["OutputArguments"],
				MapApply[fun,args],
				MapApply[{{##},fun[##]}&,args]],{Power::infy,Infinity::indet}];
	
	(*delete singularities*)
	{DeleteCases[vals,If[!OptionValue["OutputArguments"],
						ComplexInfinity|_DirectedInfinity|Indeterminate,
						{_,ComplexInfinity|_DirectedInfinity|Indeterminate}]],
	args}]


(* ::Subsubsection::Closed:: *)
(*Number digits*)


(* ::Text:: *)
(*The function which computes the number of digits in the given number 'num' and automatically sets the value of the option "SignificantDigits":*)


(* ::Input::Initialization:: *)
ClearAll[autoDigits]

autoDigits[num_?NumericQ]:=
	Block[{rdg,posnz=0},
		If[MemberQ[{Integer,Rational},Head[num]],Return[16]];
		rdg=First@RealDigits[Chop@N@num]/.{
				{PatternSequence[x__,0,0,0..,1]}:>PadRight[{x,0},16],
				{PatternSequence[x__,y_,9,9..,9]}:>PadRight[{x,y+1},16]};
		
		(*this searches the position of the first nonzero digit from the right*)
		If[rdg=!={0},
			If[$VersionNumber>=14.2,
			posnz=SelectFirst[Reverse@rdg,#!=0&->"Index"],
			While[posnz<=Length@rdg,
				posnz++;
				If[Part[Reverse@rdg,posnz]!=0,Break[]
					]]],
			posnz=1];
		Max[Length@rdg-posnz+1,2(*single digits are not allowed*)]]

autoDigits[0.|0]=1;

autoDigits[num_Complex?NumericQ]:=
	Max[autoDigits/@ReIm[num]]


(* ::Input::Initialization:: *)
precisionFilter[num_?NumericQ,arg_,digits_Integer]:=
	Abs[N[1-arg/num,digits+1]]<=10^(-digits+1)


(* ::Subsubsection::Closed:: *)
(*Formula complexity*)


(* ::Text:: *)
(*The following function returns an real value which ranks the complexity of the final and intermediate formulae, determined essentially as the sum of the means between DigitsSum and 5 times IntegerLength of all integers appearing in the formula:*)


(* ::Input::Initialization:: *)
digitSum[int_Integer]:=If[$VersionNumber>=14,DigitSum[int],Total@IntegerDigits[int]]

ClearAll[formulaComplexity]

formulaComplexity[form_?NumericQ]:=
	N@Total[Cases[
			Inactivate[form]
		/.const_?(Quiet@MemberQ[Attributes[#],Constant]&):>1
			/.c_Complex:>ReIm[c]
				/.r:Rational[i1_Integer,i2_Integer]:>{i1,i2}
					/.Inactive[Sqrt][arg_]:>Inactive[Sqrt[{arg,arg}]]
						/.(b_ \!\(\*
TagBox["^",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"^"]\)(m_ \!\(\*
TagBox["*",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"a*b"]\)n_ \!\(\*
TagBox["^",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"^"]\)(-1)|{m_,n_})|{b_}\!\(\*
TagBox["^",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"^"]\)(m_ \!\(\*
TagBox["*",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"a*b"]\)n_ \!\(\*
TagBox["^",
"InactiveToken",
BaseStyle->"Inactive",
SyntaxForm->"^"]\)(-1)|{m_,n_})):>Table[b,Abs[n m]]
							,
			_Integer,{0,Infinity}]
				/.i_Integer:>Mean[{5IntegerLength[i],digitSum[i],Abs[N@i]^(1/2)}]]


(* ::Text:: *)
(*Also the argument range can be given a complexity value, which allows to increase the complexity threshold for each round:*)


(* ::Input::Initialization:: *)
formulaComplexity[list_List]:=Max@Map[formulaComplexity,list]


(* ::Subsubsection::Closed:: *)
(*Algebraic numbers*)


(* ::Text:: *)
(*The following definitions modify RootApproximant so to safely deal with undefined and singular values. This will be used to compute linear combinations of the functional form through simple algebraic numbers (see below the options "AlgebraicAdd" and "AlgebraicFactor").*)


(* ::Input::Initialization:: *)
(*this cell block takes about 2 seconds to evaluate*)
(*this lookup table choice is somewhat arbitrary but can be customised through the option RootApproximantMethod*)
absLookupBase:=absLookupBase=SortBy[
Flatten@Union[Range[100000000,10^9,10^5],Range[1000000,100000000,1000],Range[100000,1000000,10],Range[10000,100000],Range[0,10000,1/10],ResourceFunction["FareyRange"][0,1000,10],ResourceFunction["FareyRange"][0,100,100],Sqrt@ResourceFunction["FareyRange"][0,100,50],(#)^(1/3)&/@ResourceFunction["FareyRange"][0,100,10],(#)^(1/4)&/@ResourceFunction["FareyRange"][0,100,10],(#)^(1/5)&/@ResourceFunction["FareyRange"][0,100,10],(#)^(1/6)&/@ResourceFunction["FareyRange"][0,100,10]],N];
absLookupBaseN:=absLookupBaseN=N[absLookupBase];
(*in case complex numbers are searched for*)
phaseLookupBase:=phaseLookupBase=ResourceFunction["FareyRange"][-1,1,100];
phaseLookupBaseN:=phaseLookupBaseN=N[phaseLookupBase];


(* ::Input::Initialization:: *)
(*the global symbols absLookup and absLookupN are set later by the main function*)

(*to avoid 2 s delay on the first evaluation, evaluate them immediately as follows*)

(*the following If is a hack to evaluate them immediately upon initialization, without blocking resource tools Check, Preview and Submit (for some reason they get stuck in examining the content this heavy symbols*)
(*for some reason after pressing Check you should also quit the kernel to avoid some delay*)
(*If[True,
	absLookup=absLookupBase;
	absLookupN=absLookupBaseN;
	phaseLookup=phaseLookupBase;
	phaseLookupN=phaseLookupBaseN;];*)


(* ::Input::Initialization:: *)
(*eliminate singular forms*)
freeSingular=FreeQ[#,ComplexInfinity|_DirectedInfinity|Indeterminate]&;
freeSymbol=Apply[And,Map[FreeQ[#,_Symbol]&,ReIm@N@#]]&;


(* ::Input::Initialization:: *)
ClearAll[modifiedRootApproximant,modifiedRootApproximantMain]

modifiedRootApproximantMain[r_,options:OptionsPattern[FindClosedForm]]:=
Which[OptionValue["RootApproximantMethod"]===Automatic||Head[OptionValue["RootApproximantMethod"]]===List,
	Block[{posphase,phase,posabs,abs},
		(*we should account for a complex phase too*)
		posphase=ResourceFunction["SortedPosition"][
						phaseLookupN,-I/\[Pi] Log[r/Abs[r]]];
		If[Length[posphase]==2&&Last[posphase]>Length[phaseLookupN],posphase=posphase[[1]]];
		phase=Which[Positive[r],1,
					Positive[-r],-1,
					True,
					Exp[I \[Pi] phaseLookup[[posphase]]]];
		posabs=ResourceFunction["SortedPosition"][absLookupN,Abs[r]];
		If[Length[posabs]==2&&Last[posabs]>Length[absLookupN],posabs=posabs[[1]]];
		abs=absLookup[[posabs]];
		If[Head[phase]===List&&Head[abs]===List,
			Flatten@Outer[Times,phase,abs],
			phase *abs]],
	OptionValue["RootApproximantMethod"]==="BuiltIn",
	RootApproximant[r]]

modifiedRootApproximant[r_,options:OptionsPattern[FindClosedForm]]:=modifiedRootApproximantMain[r,options]

modifiedRootApproximant[s_?(!freeSingular),options:OptionsPattern[FindClosedForm]]:=Indeterminate;
modifiedRootApproximant[s_?(!FreeQ[#,_Symbol]&),options:OptionsPattern[FindClosedForm]]:=
	Block[{sn},
		sn=N[s];
		If[freeSymbol[sn],
			modifiedRootApproximantMain[sn,options],
			Indeterminate]]


(* ::Text:: *)
(*Higher roots of relatively simple form which will be kept, but complicated and uninteresting approximate roots are to be deleted:*)


(* ::Input::Initialization:: *)
deletedRootPatterns=HoldPattern[_->_?(!FreeQ[#,Root]&)];


(* ::Subsubsection::Closed:: *)
(*Rational simplification*)


(* ::Text:: *)
(*A replacement function to round and simplify rationals:*)


(* ::Input::Initialization:: *)
ClearAll[orderMagnitude]
orderMagnitude[x_?NumericQ]:=Block[{log,digits,first},
						log=Floor[Log10[Abs[x]]];
						digits=First@RealDigits[N@x];
						first=First@digits;
						Which[first<5,log,first>5,log+1,first==5&&digits[[2]]<=5,log,first==5&&digits[[2]]>5,log+1]]
orderMagnitude[x_Complex?NumericQ]:=
	Max[orderMagnitude/@Chop@N@ReIm[x]]


ClearAll[simplifyRational]
simplifyRational[num_?NumericQ,fun_Function,digits_?Positive,complexity:_?Positive|Infinity,operation_Symbol,form_]:=
	
	r:Rational[n_Integer,m_Integer]:>
		
		If[fun=!=Function@Identity[#](*the rationals are to be kept if the function searched is the Identity*),
			
			Block[{round,precQ,ordr,cont,fc,contsimp},
				
				round=Round[r,Min[Power[10,-digits+orderMagnitude[r]],
									Power[10,-digits+orderMagnitude[num]]]];
				
				(*check whether the precision of the match increases or not, otherwise discard the simplication*)
				precQ=precisionFilter[num,operation[#,form],digits]&;

				(*rounding does not work for periodic rationals, so truncate their continued fraction*)
				If[formulaComplexity[round]<=2formulaComplexity[r],

					If[formulaComplexity[round]<=complexity&&precQ[round],
						
						round,

						ordr=orderMagnitude[round]+1;
						cont=ContinuedFraction[round];
						fc=Power[10,orderMagnitude@Max[Abs@cont[[1]],1]];
						contsimp=FromContinuedFraction@
								ReplaceAll[
									cont,
									{{x1_,y_?(Abs@#>=fc Power[10,Max[5-ordr,5]]&),z___}:>{x1},
									{x1_,xr__,y_?(Abs@#>=fc Power[10,Max[4-ordr,4]]&),z___}:>{x1,xr},
									{x1_,x2_,xr__,y_?(Abs@#>=fc Power[10,Max[3-ordr,3]]&),z___}:>{x1,x2,xr}}];
						If[precQ[contsimp],
							contsimp,
							r]
						],
					r]],

			r]


(* ::Subsection::Closed:: *)
(*Wolfram Alpha*)


(* ::Text:: *)
(*This function queries closed forms directly from WolframAlpha, but restricts the result to match the desired number of digits and of limited complexity.*)


(* ::Input::Initialization:: *)
ClearAll[queryWA]
queryWA[num_?NumericQ,digits_?Positive,complexity:_?Positive|Infinity,res_]:=
	Block[{quernum,queries,queriesprec,queriescompl},
		quernum=Round@res;
		queries=Quiet[
				Which[quernum==0,
					{Missing[]},
					1<=quernum<=3,	
					Table[
					WolframAlpha[ToString[num],
								{{"PossibleClosedForm",i},"FormulaData"}],
					{i,1,quernum}],
					4<=quernum,
					Table[
					WolframAlpha[ToString[num],
								{{"PossibleClosedForm",i},"FormulaData"},
								PodStates->{"PossibleClosedForm__More"}],
					{i,1,If[quernum<=10,quernum,10]}]],{URLFetch::invhttp(*,WolframAlpha::timeout*)}];
		queries=Map[Apply[Apply@Rule,#]&,DeleteMissing@queries];
		queries=DeleteMissing@Keys@queries;
		queries=Select[ToRadicals@queries,(!MatchQ[#,_Rational]&&FreeQ[#,_Root])&];
		queriesprec=Select[queries,precisionFilter[num,#,digits]&];
		queriescompl=Select[queriesprec,formulaComplexity[#]<=complexity&]]


(* ::Subsection:: *)
(*Search round*)


(* ::Subsubsection::Closed:: *)
(*Sub search round*)


(* ::Text:: *)
(*The elementary argument search function, depending on the operation ("Times", "Plus" or "None") used to search for extra algebraic numbers in the formula:*)


(* ::Input::Initialization:: *)
ClearAll[subSearchRound]
subSearchRound[num_?NumericQ,fun_Function,range_List,rangePrev_Association,digits_?Positive,complexity:_?Positive|Infinity,operation_String,options:OptionsPattern[FindClosedForm]]:=
	Block[{rootoper,precoper,compoper,replrational,complexQ,precPatt,complPatt,argQ,
		rangecollect,comb,nrange,algeb,result,simpresult},

		(*operation for RootApproximant*)
		rootoper=Quiet[
				
					Which[operation=="Times",
						modifiedRootApproximant[num/#,options],
						operation=="Plus",
						modifiedRootApproximant[num-#,options]],
					{Power::infy,Infinity::indet}]&;
		
		(*operation for precision check*)
		precoper=Which[
					operation=="Times",
						If[
						freeSymbol[#[[1]]],
						#[[1]]#[[2]]],
					operation=="Plus",
						If[
						freeSymbol[#[[1]]],
						#[[1]]+#[[2]]],
					operation=="None",
						If[
						freeSymbol[#],
						#]]&;

		precPatt[arg_]:=precisionFilter[num, precoper[arg],digits];

		(*final composition operation*)
		compoper=Which[
					operation==="Times",
						Times,
					operation==="Plus",
						Plus,
					operation==="None",
						Identity];

		complPatt[arg1_,arg2___]:=If[operation=!="None",
										formulaComplexity[Replace[compoper[arg1,arg2],replrational[compoper,arg1],1]]
											<=complexity,
										formulaComplexity[arg1]<=complexity];
										
		rangecollect=rangePrev;
	
		replrational[oper_,form_]:=simplifyRational[num,fun,digits,complexity,oper,form];

		complexQ=Im[num]==0;

		argQ=OptionValue["OutputArguments"];

		(*evaluation of funcional form over the previous range*)
		{comb,nrange}=functionValues[
						fun,
						range,
						rangePrev[operation],
						"Operation"->operation,
						"ComplexArg"->OptionValue["SearchComplex"],
						"RealValued"->complexQ,
						"SearchArguments"->OptionValue["SearchArguments"],
						"OutputArguments"->argQ];
		
		(*update of range*)
		rangecollect[operation]=Union[rangecollect[operation],nrange];
		
		If[operation!="None",
		
		(*compuation of additional algebraic numbers*)
		(*parallelization must change*)
			algeb=If[!OptionValue["OutputArguments"],
					AssociationMap[rootoper,comb],
					AssociationMap[rootoper[#[[2]]]&,comb]];
		
		(*elimination of singularities*)
			algeb=Select[algeb,freeSingular];
			algeb=KeySelect[algeb,freeSingular];
			
			
			If[OptionValue["RootApproximantMethod"]==="BuiltIn",	
			(*elimination of complicated roots*)
			algeb=DeleteCases[Normal@algeb//ToRadicals
									(*keep simple higher roots*),
									deletedRootPatterns]];


			(*eliminate invalid approximations*)
			algeb=Cases[
						If[!argQ,
							ReplaceAll[Normal@algeb,
										p:HoldPattern[_->_List]:>Thread[p]],
							ReplaceAll[Normal@algeb,
										HoldPattern[{x1_,x2_}->l_List]:>
											MapAt[Append[{x1},#]&,Thread[x2->l],{All,1}]]]
						//Flatten,
						If[!argQ,
							HoldPattern[_->_]?(precPatt[#]&),
							HoldPattern[_->_]?(precPatt[{#[[1,2]],#[[2]]}]&)]];

			(*eliminate complex formulae*)
			algeb=Cases[
						Normal@algeb,
						If[!argQ,
							HoldPattern[_->_]?(complPatt[#[[1]],#[[2]]]&),
							HoldPattern[_->_]?(complPatt[#[[1,2]],#[[2]]]&)]];
		
			If[algeb=!={}(*<||>*),
				(*reconstruct the result*)
				result=Union@MapApply[If[!argQ,compoper[##],{#1[[1]],compoper[#1[[2]],#2]}]&,algeb];
	
			If[(*unless the function is the identity, eliminate rational solutions*)
			(fun=!=Function@Identity[#]
				&&(!OptionValue["RationalSolutions"])
				&&If[Length[result]==1,
					If[!argQ,
						Head[result[[1]]]===Rational,
						Head[result[[1,2]]]===Rational],
					If[!argQ,
						result=DeleteCases[result,_Rational],
						result=DeleteCases[result,{_,_Rational}]];False]),

				Return[{{},rangecollect}],
	
				simpresult=Union@MapApply[
							If[!argQ,
								Replace[compoper[##],replrational[compoper,#1],1],
								{#1[[1]],Replace[compoper[#1[[2]],#2],replrational[compoper,#2],1]}]&,
							algeb];
				Return[{simpresult,rangecollect}]

				],

				Return[{{},rangecollect}]],
		
			(*simplified module in case no extra algebraic number is searched*)
			comb=Select[comb,freeSingular];
			comb=Cases[comb,
							If[OptionValue["OutputArguments"],
								_?(precisionFilter[num,precoper[#[[2]]],digits]&),
								_?(precisionFilter[num,precoper[#],digits]&)]];
			result=Cases[comb,
							If[OptionValue["OutputArguments"],
								_?(formulaComplexity[#[[2]]]<=complexity&),
								_?(formulaComplexity[#]<=complexity&)]];
			Return[{result,rangecollect}]];
	
		]


(* ::Subsubsection::Closed:: *)
(*Search round*)


(* ::Text:: *)
(*The basic argument search round:*)


(* ::Input::Initialization:: *)
ClearAll[searchRound]

searchRound[num_?NumericQ,fun_Function,res_Integer,cut_Integer,rangePrev_Association,digits_?Positive,complexity:_?Positive|Infinity,options:OptionsPattern[FindClosedForm]]:=
	searchRound[num,fun,res,rangeFull[cut,"ComplexArg"->OptionValue["SearchComplex"],"SearchRange"->OptionValue["SearchRange"]],rangePrev,digits,complexity,options]

searchRound[num_?NumericQ,fun_Function,res_Integer,rangeAss_Association,rangePrev_Association,digits_?Positive,complexity:_?Positive|Infinity,options:OptionsPattern[FindClosedForm]]:=
	searchRound[num,fun,res,Lookup[rangeAss,slotArgs[fun]],rangePrev,digits,complexity,options]

searchRound[num_?NumericQ,fun_Function,res_Integer,range_List,rangePrev_Association,digits_?Positive,complexity:_?Positive|Infinity,options:OptionsPattern[FindClosedForm]]:=
	Block[{rangecollect,resN,resT,resP,result},
		
		rangecollect=rangePrev;
		
		{resN,rangecollect}=subSearchRound[num,fun,range,rangecollect,digits,complexity,"None",options];
		If[resN=!={}&&Length[resN]>=res,Return[{resN,rangecollect}]];	

		If[OptionValue["AlgebraicFactor"],
		{resT,rangecollect}=subSearchRound[num,fun,range,rangecollect,digits,complexity,"Times",options];
		If[resT=!={}&&Length[resN]+Length[resT]>=res,Return[{Union[resN,resT],rangecollect}]],
		resT={};];

		If[OptionValue["AlgebraicAdd"],
		{resP,rangecollect}=subSearchRound[num,fun,range,rangecollect,digits,complexity,"Plus",options];
		If[resP=!={}&&Length[resN]+Length[resT]+Length[resP]>=res,Return[{Union[resT,resP,resN],rangecollect}]],
		resP={}];

		result=Union[resT,resP,resN];

		{result,rangecollect}]


(* ::Subsection::Closed:: *)
(*Main function*)


(* ::Text:: *)
(*Finally the main function, calling the argument search round and further searching over the list of functional forms:*)


(* ::Input::Initialization:: *)
ClearAll[FindClosedForm]
Options[FindClosedForm]={"SignificantDigits"->Automatic,"FormulaComplexity"->Automatic,"WolframAlphaQueries"->3,"SearchQueries"->Automatic,"MonitorSearch"->False,"AlgebraicFactor"->True,"AlgebraicAdd"->True,"RootApproximantMethod"->Automatic,"RationalSolutions"->False,"SearchArguments"->Automatic,"OutputArguments"->False,"SearchRange"->"Farey","SearchComplex"->False,"MaxSearchRounds"->50,"SearchTimeLimit"->3600};

(*main function distinct from FindClosedForm[num,funL,res,options] because of the argument WAres, used to avoid duplication of WolframAlpha results*) 

mainFindClosedForm[num_?NumericQ,funL_List,res_Integer,WAres_List,options:OptionsPattern[FindClosedForm]]/;SubsetQ[{Function,Symbol},Union@Map[Head,funL]]:=
	Block[{funList,complexityF,digits,try,tryold,argQ,rtmet,args,argsout,rgval,pDo,searchblock,rangecollect,rangenew,f,resultbuild,result,resultcount},

			funList=Map[#/.slotReplace[#]&(*in case the slots are unordered*),
					Table[If[Head[fun]===Symbol,Evaluate@fun[#]&,fun],{fun,funL}]];

			digits=If[OptionValue["SignificantDigits"]===Automatic,
					autoDigits[num],
					OptionValue["SignificantDigits"]];
				
			complexityF[fn_,arg_]:=
				If[OptionValue["FormulaComplexity"]===Automatic,
					1/2(1+Sqrt@slotNumber[fn])*If[
						Length@funList>=10,
						(*possibly specify a different value with many functions, since the risk of confusion increases*)
						15+formulaComplexity[arg],
						15+formulaComplexity[arg]],
					OptionValue["FormulaComplexity"]];

			try=result={}(*the list of results*);

			argQ=OptionValue["OutputArguments"];
			args=argsout={};

			resultcount=0;

			(*function which builds the result when found*)
			resultbuild:=If[!argQ,
							(*sort the results by complexity*)
							Take[SortBy[
									DeleteCases[Union@try,
												(*delete redundant WA results*)
												Which[Length[WAres]>=2,Alternatives@@WAres,
														Length[WAres]==1,WAres[[1]],
														True,{}]],
									formulaComplexity],
								UpTo[res]],

							(*output association with arguments*)
							(*sort both results and arguments by complexity*)
							Take[KeySortBy[SortBy[
										Select[AssociationThread[argsout,try],
												!MemberQ[WAres,#]&],
										formulaComplexity],formulaComplexity],
								UpTo[res]]];
						
			(*the argument range, tracked and updated for each round, to avoid redundant evaluations*)
			rangenew=rangecollect=
					AssociationThread[
							funList,
							Table[<|"Times"->{},"Plus"->{},"None"->{}|>,Length[funList]]];

			rgval=OptionValue["SearchArguments"];

			(*determine the possible algebraic numbers appearing in the formula*)
			(*the first time this evaluates it takes 2 s more*)
			rtmet=OptionValue["RootApproximantMethod"];
			If[And[Head[rtmet]===List,rtmet=!={Automatic,Automatic}],

				Which[
				Or[Depth[rtmet]==2,Depth[rtmet]==3&&rtmet[[2]]===Automatic],
					absLookup=rtmet;
					absLookupN=N[absLookup,Max[digits,16]],
				Depth[rtmet]==3&&rtmet[[1]]===Automatic,
					phaseLookup=rtmet[[2]];
					phaseLookupN=N[phaseLookup,Max[digits,16]],
				Depth[rtmet]==3,
					{absLookup,phaseLookup}=rtmet;
					{absLookupN,phaseLookupN}=N[{absLookup,phaseLookup},Max[digits,16]]],

				absLookup=absLookupBase;
				absLookupN=absLookupBaseN;
				phaseLookup=phaseLookupBase;
				phaseLookupN=phaseLookupBaseN];


			(*the main subfunction to search over argument and function ranges*)
			searchblock:=
				
				
				Do[	
					Block[{rootnew,rg,compl,resultnew},
						(*set this parameter to the round number/cutoff or to the custom argument range*)
						
						tryold=try;

						rg=If[rgval===Automatic,cut,rgval];
						
						(*compute the complexity for each round*)
						compl=complexityF[f,
								If[rgval===Automatic,
									Flatten@rangeFull[
										cut,
										"ComplexArg"->OptionValue["SearchComplex"],
										"SearchRange"->OptionValue["SearchRange"]],
									If[Head[rgval]===Association,
										Flatten@Values@rgval,
										Flatten@rgval]]];
						
						(*evaluate the argument search round*)
						{rootnew,rangenew[f]}=
							searchRound[num,f,res,rg,rangecollect[f],digits,compl,options];
						try=If[!argQ,
								DeleteDuplicates@Join[try,rootnew],
								Join[try,Last/@rootnew]];
						If[argQ,
							args=Join[args,First/@rootnew];
							argsout=If[Length[funL]!=1,
										MapApply[Inactivate[Evaluate[f]][##]&,args],
										args]];
						rangecollect[f]=Merge[{rangecollect[f],rangenew[f]},Flatten[#,1]&];
						
						(*print temporarily the results found*)
						(*end the function search round if all required results are found*)
						If[Length[try]>=Length[tryold],

							resultnew=Drop[try,Length[tryold]];
							
							MapIndexed[
								PrintTemporary[
									"Search result "<>ToString[resultcount+#2[[1]]]<>": ",
									#]&,
								resultnew];
							resultcount=resultcount+Length[resultnew];

							result=resultbuild;

							If[Length[result]==res,Return[result]]];],

						(*loop over the argument and function search rounds*)
						Evaluate@If[OptionValue["SearchArguments"]===Automatic,
								Sequence@@{
									{cut,1,OptionValue["MaxSearchRounds"]},
									{f,funList}},
								{f,funList}]];
			
			(*allow safe abort returning partial results even if not all of them are found*)
			CheckAbort[
				(*abort beyond the search time limit*)
				TimeConstrained[
					If[rgval===Automatic,
			
						If[!OptionValue["MonitorSearch"],
							searchblock,
							(*monitor round and function*)
							Monitor[
								searchblock,
								If[Length[funList]==1,cut,{cut,f}]]],
			
						If[!OptionValue["MonitorSearch"],
							searchblock,
							(*monitor only function with custom argument range*)
							Monitor[
								searchblock,
								f]]
						],
					OptionValue["SearchTimeLimit"]],

				If[#==={}||#===<||>,Return[$Aborted],#]&@
					resultbuild];
				
				result]


(*the most general defintion*)

FindClosedForm[num_?NumericQ,funL_List,res_Integer,options:OptionsPattern[FindClosedForm]]/;SubsetQ[{Function,Symbol},Union@Map[Head,funL]]:=
	mainFindClosedForm[num,funL,res,{},options]


(*specify only the number and search over the most common single argument functions*)
(*call WA only in this case*)

FindClosedForm[num_?NumericQ,res_Integer,options:OptionsPattern[FindClosedForm]]:=
	Block[{funList,digits,complexity,resultWA,searchqueries,resultS},

			digits=If[OptionValue["SignificantDigits"]===Automatic,
					autoDigits[N@num],
					OptionValue["SignificantDigits"]];
			
			complexity=If[OptionValue["FormulaComplexity"]===Automatic,50,OptionValue["FormulaComplexity"]];

			resultWA=queryWA[num,digits,complexity,
							Min[Max[res,OptionValue["WolframAlphaQueries"]],OptionValue["WolframAlphaQueries"]]];

			If[Length[resultWA]>=res,Return[Take[resultWA,UpTo[res]]]];

			If[Length[resultWA]>=1,MapIndexed[PrintTemporary["WolframAlpha result "<>ToString@#2[[1]]<>": ",#]&,resultWA]];
			
			searchqueries=If[OptionValue["SearchQueries"]===Automatic,
								res-Length[resultWA],
								Min[OptionValue["SearchQueries"],res-Length[resultWA]]];

			If[searchqueries==0,Return[resultWA]];

			funList={\[Pi]^#&,EulerGamma^#&,Catalan^#&,
					GoldenRatio^#&,Glaisher^#&,Khinchin^#&,
					Sin[\[Pi] #]&,Cos[\[Pi] #]&,Tan[\[Pi] #]&,
					ArcSin[#]&,ArcCos[#]&,ArcTan[#]&,ArcCot[#]&,
					Log[#]&,Exp[#]&,Sinh[#]&,Cosh[#]&,Tanh[#]&,
					ArcSinh[#]&,ArcCosh[#]&,ArcTanh[#]&,ArcCoth[#]&,
					Zeta[#]&,Gamma[#]&,PolyGamma[#]&,
					EllipticK[#]&,EllipticE[#]&,
					Erf[#]&,InverseErf[#]&,BarnesG[#]&,
					AiryAi[#]&,AiryBi[#]&};
			
			If[OptionValue["SearchComplex"],
				(*these functions are not defined for real arguments*)
				funList=Join[funList,
					{DedekindEta[#]&,ModularLambda[#]&}]];

			resultS=mainFindClosedForm[num,funList,searchqueries,resultWA,options];
						
			If[resultS=!=$Aborted,
				If[Head[resultS]=!=Association,
					DeleteDuplicates@Join[resultWA,resultS],
					Join[resultWA,{resultS}]],
				$Aborted]]

(*only one result, the most common case*)

FindClosedForm[num_?NumericQ,funL___List,options:OptionsPattern[FindClosedForm]]:=
	Block[{search},
	search=FindClosedForm[num,funL,1,options];
	If[Length@search==1,If[Head[search]===Association,search,First@search],If[search===$Aborted,$Aborted,None]]]

(*specify only one functional form*)

FindClosedForm[num_?NumericQ,f:_Function|_Symbol,res___Integer,options:OptionsPattern[FindClosedForm]]:=
	FindClosedForm[num,{f},res,options]

(*use the identify functional form as symbol*)

FindClosedForm[num_?NumericQ,Identity,res___Integer,options:OptionsPattern[FindClosedForm]]:=
	FindClosedForm[num,{Identity[#]&},res,options]


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
