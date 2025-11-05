(* ::Package:: *)

(* ::Title:: *)
(*ThermodynamicBetheAnsatzSolve (1.0.0)*)


(* ::Subtitle:: *)
(*Wolfram Resource Function contributed by: Daniele Gregori*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["TBA`"];


ThermodynamicBetheAnsatzSolve::usage=
"ThermodynamicBetheAnsatzSolve[eqn]
  solves a TBA equation.

ThermodynamicBetheAnsatzSolve[eqn, y]
  solves a TBA and returns the value of the solution.

ThermodynamicBetheAnsatzSolve[{eqn1, eqn2, \[Ellipsis]}]
  solves a system of TBA equations.

ThermodynamicBetheAnsatzSolve[{eqn1, eqn2, \[Ellipsis]}, {y1, y2, \[Ellipsis]}]
  solves a system of TBA equations and returns the specified solutions values.";


Begin["Private`"];


(* ::Section:: *)
(*Definition*)


(* ::Subsection::Closed:: *)
(*Error management*)


(* ::Subsubsection:: *)
(*Possible failures*)


(* ::Input::Initialization:: *)
overflowFailure=Failure["TBAOverflow","MessageTemplate"->"Overflow detected: the Thermodynamic Bethe Ansatz is likey to be non-convergent for the specified parameters."];


(* ::Input::Initialization:: *)
intVarFailure=Failure["IntegrationVariable",
			"MessageTemplate"->"Please use a single integration variable"];


(* ::Input::Initialization:: *)
multiVarFailure=Failure["Multivariables",
				<|"MessageTemplate"->"Cannot solve the TBA equation for multiple variables: `vars`",
				"MessageParameters"-><|"vars"->#|>|>]&;


(* ::Input::Initialization:: *)
depVarFailure=Failure["DependentVariable",
						<|"MessageTemplate"->"The requested symbols `symb` do not belong to the dependent variables `dep`",
						 "MessageParameters"-><|"symb"->#1,"dep"->#2|>|>]&;


(* ::Input::Initialization:: *)
lhsFailure=Failure["LHS",
						<|"MessageTemplate"->"Please write on the left hand side only the dependent variables"|>];


(* ::Input::Initialization:: *)
bdyFailure=Failure["BoundaryList",
								<|"MessageTemplate"->"The boundary condition `bdy` has not the right dimensions",
								"MessageParameters"-><|"bdy"->#|>|>]&;


numFailure=Failure["NonNumeric",
							<|"MessageTemplate"->"Please give numeric values to the TBA parameters"|>];


(* ::Subsubsection:: *)
(*Throw failure*)


(* ::Input::Initialization:: *)
failureThrow[arg_]:=
	If[MemberQ[arg,_Failure,{0,Infinity}],
		Throw@First@Union@Cases[arg,_Failure,{0,Infinity}],
		arg]


(* ::Subsection::Closed:: *)
(*Equation preprocessing*)


(* ::Subsubsection:: *)
(*Main terms*)


integrals[intEq_Equal]:=
	Block[{lists},
		lists=Map[If[Head[#]===Plus,List@@#,{#}]&,List@@intEq];
		Map[If[Head[#]===Plus,List@@#,{#}]&,Expand[Select[Join[lists[[2]],-lists[[1]]],!FreeQ[#,_Integrate,{0,Infinity}]&]]]//Flatten//List]
		
integrals[intEq_List]:=
	Map[First@*integrals,intEq]
	
outers[intEq_Equal]:=
	Block[{lists,sels},
		lists=Map[If[Head[#]===Plus,List@@#,{#}]&,List@@intEq];
		sels=Map[Select[#,FreeQ[#,_Integrate,{0,Infinity}]&]&,lists];
		Plus@@sels[[1]]==Plus@@sels[[2]]]
		
outers[intEq_List]:=
	Map[outers,intEq]


(* ::Input::Initialization:: *)
integrands[intEq_]:=
	integrals[intEq]/.
		i_Integrate:>i[[1]]/.
			HoldPattern@List[a___,p:Times[___,Plus[_Log..],___],b___]:>List[a,Sequence@@Distribute[p],b]


(* ::Subsubsection:: *)
(*Variables*)


(* ::Input::Initialization:: *)
variableInt[intEq_]:=
	Block[{all,un},
		all=Map[Cases[#,i_Integrate:>i[[2,1]],\[Infinity]]&,integrals[intEq]];
		un=Union@Flatten@all;
		If[Length@un>1,
		Return[
		intVarFailure],
		un[[1]]]]

limitsInt[intEq_]:=
	Map[Cases[#,i_Integrate:>i[[2,2;;]],\[Infinity]]&,integrals[intEq]]


variableDep[intEq_]:=
	If[Context[#]==="System`",Nothing,#]&/@Cases[outers[intEq],y_[x_]:>y,Infinity]

variableDepInt[intEq_]:=
	If[Context[#]==="System`",Nothing,#]&/@Cases[integrals[intEq],y_[x_]:>y,Infinity]

variableInd[intEq_]:=
	Block[{un},
		un=Union@Cases[
				Cases[outers[intEq],
						If[Length[#]===1,First[#],Apply[Alternatives,#]]&@
							Map[#[x_]&,variableDep[intEq]],
						Infinity],
						y_[x_]:>x];
		If[Length[un]>1,
			multiVarFailure[un],
			un[[1]]]]
		


(* ::Subsubsection:: *)
(*Forcing, kernels, L functions*)


forcing[intEq_]:=
	Cases[outers[intEq],_?(FreeQ[#,Alternatives@@variableDep[intEq]]&),{2}]
	
kernels[intEq_]:=
	ReplaceAll[		
			Map[
				Apply[#[[1]],#[[2]]]&@
				{Head[#],Cases[#,_?(FreeQ[#,Alternatives@@variableDep[intEq]]&)]}&,
				integrands[intEq],{2}],
				variableInd[intEq]:>variableInt[intEq]+variableInd[intEq]]/.p_Plus:>Expand@Simplify@p

crossingDep[intEq_]:=
	Block[{rule},
		rule=MapThread[#1->variableDepInt[#2]&,{variableDep[intEq],integrals[intEq]}];
		Map[DeleteCases[First@Flatten@Position[Keys@rule,#],{}]&,Values@rule,{2}]]
		
functionsL[intEq_]:=
	Simplify[integrands[intEq]/
				ReplaceAll[
					kernels[intEq],
					variableInd[intEq]:>-variableInt[intEq]+variableInd[intEq]]]
			
constants[intEq_]:=functionsL[intEq]/.
						{Log[1+Times[c__,Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)]]]:>c,
						Log[1+Times[Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)],c__]]:>c,
						Log[1+Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)]]:>1}


(* ::Input::Initialization:: *)
signs[intEq_]:=Map[If[MatchQ[#,Times[-1,_]],-1,1]&,PowerExpand[functionsL[intEq]/.
						{Log[1+Times[__,exp:Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)]]]:>Log@exp,
						Log[1+Times[exp:Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)],__]]:>Log@exp,
						Log[1+exp:Exp[_?(MemberQ[#,variableInt[intEq],\[Infinity]]&)]]:>Log@exp}],{2}]


(* ::Input::Initialization:: *)
padding[list_List]:=
Block[{max},
max=Max[Length/@list];
Map[PadRight[#,max,0]&,list]]


(* ::Subsection::Closed:: *)
(*Main function*)


ClearAll[ThermodynamicBetheAnsatzSolve]

Options[ThermodynamicBetheAnsatzSolve]=
		{"BoundaryCondition"->{0,0},
		"StoppingAccuracy"->10^(-10),
		MaxIterations->4000,
		"MonitorIterations"->False,
		"GridCutoff"->Automatic,
		"GridResolution"->2^10,
		"SaveMemory"->False};
		
ThermodynamicBetheAnsatzSolve[intEq_Equal|intEq:{_Equal..},options:OptionsPattern[ThermodynamicBetheAnsatzSolve]]:=
	Block[{dep},
		dep=variableDep[intEq];
		List@Normal@
			AssociationThread[dep,ThermodynamicBetheAnsatzSolve[intEq,dep,options]//failureThrow]]//Catch

ThermodynamicBetheAnsatzSolve[tba_Equal|tba:{_Equal..},y_Symbol|y:{_Symbol..},options:OptionsPattern[ThermodynamicBetheAnsatzSolve]]:=
	ResourceFunction["CheckReturn"][
	ResourceFunction["CheckReturn"][
		Block[
		{intEq,numberEq,vI,vD,x0,
		iterations,cut,res,
		ker,kerFTab,
		cnst,crossing,sgn,
		forc,forcTab,
		bd,bdBuild,
		bdyExt,bdyInt,boundaryIntTab,
		phaseTab,convFourier,
		intIteration,intIterationCache,
		solutionTable,interpolFun,solutionInterpolation,
		solutionFinal,assocFinal,
		nStop,errors},
		
		intEq=Flatten@{tba};
		
		numberEq=Length@intEq;
		
		vI=variableInd[intEq]//failureThrow;
		
		vD=variableDep[intEq];
		
		If[!SubsetQ[vD,Flatten@{y}],
			depVarFailure[Flatten@{y},vD]]//failureThrow;
			
		If[Union@vD=!=Union[Head/@intEq[[All,1]]],
			lhsFailure]//failureThrow;
		
		
		res=OptionValue["GridResolution"];
		
		cut=With[{cutDef=100.2},
				If[OptionValue["GridCutoff"]===Automatic,
					If[NumberQ[#],#,cutDef]&@Max@Union@Flatten@limitsInt[intEq],
					OptionValue["GridCutoff"]]];

		
		x0[i_,rs_,ct_]:=-ct+ 2ct (i-1) /rs;
		
		
		ker=kernels[intEq]//failureThrow;
		
	 
		kerFTab=Map[Fourier[#,FourierParameters->{1,-1}]&,
					Map[N[#/.
							vI->Table[x0[i,res,cut],{i,1,res}]]&,
						ker,
						{2}],
					{2}];	
					
		
		bd=OptionValue["BoundaryCondition"];
		
		bdBuild[b_,s_]:=
			If[Head[b]=!=List,
					Which[
						s=="Ext",Table[b,numberEq],
						s=="Int",Table[Table[b,Length[ker[[i]]]],{i,numberEq}]],
					If[
						Which[
							s=="Ext",Length[b]===numberEq,
							s=="Int",Length[b]===numberEq&&(Length/@b===Length/@ker)],
						b,
						bdyFailure[b]]]//failureThrow;
		
		
		bdyExt=bdBuild[bd[[1]],"Ext"];
		bdyInt=bdBuild[bd[[2]],"Int"];
		
		boundaryIntTab=Map[N[#/.
								vI->Table[x0[k,res,cut],{k,1,res}]]&,
							bdyInt,
							{2}];
					
					
		forc=forcing[intEq];			
		
		forcTab=Map[N[If[MemberQ[#,vI,{0,Infinity}],
						#/.vI->Table[x0[k,res,cut],{k,1,res}],
						Table[#,res]]]&,
					forc+bdyExt];
						
		cnst=constants[intEq]//failureThrow;
		
		crossing=crossingDep[intEq]//failureThrow;	
		
		sgn=signs[intEq];
		
		phaseTab=N[Table[(2 cut)/res Exp[-I \[Pi] (j-1)],{j,1,res}]];
		convFourier[listF_, list_]:=
			InverseFourier[
				N[phaseTab*listF*
					Fourier[
						N[list], 
						FourierParameters->{1,-1}]
				],
				FourierParameters->{1,-1}];
					
		
		intIteration[solutionOld_]:=
			Block[{funsL,convcomb,
					\[Alpha],solutionNew},
				
					funsL=MapThread[
								Log[1+#2 Exp[#3*solutionOld[[#1]]]]&,
								padding/@{crossing,cnst,sgn},
								2];
				
					convcomb=MapThread[
								Plus@@Table[convFourier[#2[[i]],#1[[i]]+#3[[i]]],
											{i,1,Length[#2]}]&,
										{funsL,kerFTab,boundaryIntTab}];
				
					\[Alpha]=1/10;
					
					solutionNew=\[Alpha] solutionOld+(1-\[Alpha])(forcTab+convcomb)];


		
		solutionTable[0]=forcTab;
		
		If[OptionValue["SaveMemory"]&&$VersionNumber>=12.1,
			intIterationCache=CreateDataStructure["LeastRecentlyUsedCache",2];
			solutionTable[n_]:=
				Block[{compute,previous},
					previous=intIterationCache["Lookup",n];
					If[
					!MissingQ[previous],
					previous,
					(compute =
					 intIteration[
						solutionTable[n-1]];
					intIterationCache["Insert",n->compute];
					compute) 
					]],
			solutionTable[n_]:=
				solutionTable[n]=
					intIteration[solutionTable[n-1]]];

		
		errors[n_]:=Map[
						Max,
						Transpose/@
								Map[
									ReIm,
									2(solutionTable[n]-solutionTable[n-1])/(solutionTable[n]+solutionTable[n-1]),
									{2}],
						{2}];
		
		
		nStop:=Block[{n,errthresh=OptionValue["StoppingAccuracy"],maxiter=OptionValue[MaxIterations]},
						Flatten@Last@Reap[
										For[n=1,
											n<maxiter/100,
											n++,
											If[And@@Thread[
														Max/@errors[100n]<Table[errthresh,numberEq]],
												Break[]]];
											Sow[100n]]][[1]];
			
		
		iterations=If[OptionValue["MonitorIterations"],
						If[$Notebooks,
							Echo[Monitor[nStop,100 n],"total iterations: "],
							Echo[nStop,"total iterations: "]],
						nStop];
							
		interpolFun[fun_,rs_,ct_]:=Interpolation[Table[{x0[i,rs,ct],fun[[i]]},{i,1,rs}]];

		solutionInterpolation[j_,n_,rs_,ct_]:=interpolFun[solutionTable[n][[j]],rs,ct];			
		
		solutionFinal=Table[solutionInterpolation[j,iterations,res,cut],{j,numberEq}];

		assocFinal=AssociationThread[vD,solutionFinal];
		
		Lookup[assocFinal,y]],
		numFailure,Fourier::fftl],
		overflowFailure,General::ovfl]//Catch
		


(* ::Section:: *)
(*TBA examples*)


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
