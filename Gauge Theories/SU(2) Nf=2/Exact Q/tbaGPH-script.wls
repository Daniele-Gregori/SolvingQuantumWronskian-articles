#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Title:: *)
(*Script Q from TBA for Generalized Perturbed Hairpin IM*)


(* ::Author:: *)
(*Daniele Gregori*)


(* ::Section:: *)
(*Setup*)


(* ::Subsection:: *)
(*Resources*)


ThermodynamicBetheAnsatzSolve=ResourceFunction["ThermodynamicBetheAnsatzSolve"];


(* ::Subsection::Closed:: *)
(*Mail*)


(*
fill with your own
SetOptions[SendMail,
MailSettings-><|
    "Server"->"",
    "PortNumber"->,
    "EncryptionProtocol"->"",
    "Username"->"",
    "Password"->"",
    "FromAddress"->""
|>];*)


(* ::Section:: *)
(*Definitions*)


(* ::Subsection:: *)
(*Main*)


(* ::Subsubsection:: *)
(*TBA*)


\[Phi]GHP[x_]:=1/(2 \[Pi] Cosh[x])
tbaGHP={y1[x]==(8 Sqrt[\[Pi]^3])/Gamma[1/4]^2 Exp[x]-I \[Pi] (q1-q2)-\!\( 
\*SubsuperscriptBox[\(\[Integral]\), \(-K\), \(K\)]\(\[Phi]GHP[x - t] \((Log[1 + Exp[\(-y2[t]\)]] + Log[1 + Exp[\(-y3[t]\)]])\) \[DifferentialD]t\)\),
y2[x]==(8 Sqrt[\[Pi]^3])/Gamma[1/4]^2 Exp[x]-I \[Pi] (q1+q2)-\!\( 
\*SubsuperscriptBox[\(\[Integral]\), \(-K\), \(K\)]\(\[Phi]GHP[x - t] \((Log[1 + Exp[\(-y1[t]\)]] + Log[1 + Exp[\(-y4[t]\)]])\) \[DifferentialD]t\)\),
y3[x]==(8 Sqrt[\[Pi]^3])/Gamma[1/4]^2 Exp[x]+I \[Pi] (q1+q2)-\!\( 
\*SubsuperscriptBox[\(\[Integral]\), \(-K\), \(K\)]\(\[Phi]GHP[x - t] \((Log[1 + Exp[\(-y1[t]\)]] + Log[1 + Exp[\(-y4[t]\)]])\) \[DifferentialD]t\)\),
y4[x]==(8 Sqrt[\[Pi]^3])/Gamma[1/4]^2 Exp[x]+I \[Pi] (q1-q2)-\!\( 
\*SubsuperscriptBox[\(\[Integral]\), \(-K\), \(K\)]\(\[Phi]GHP[x - t] \((Log[1 + Exp[\(-y2[t]\)]] + Log[1 + Exp[\(-y3[t]\)]])\) \[DifferentialD]t\)\)};
CGHP[P_,q1_,q2_]:=
Log[(2^(1-2P)P Gamma[2P]^2)/Sqrt[Gamma[P+1/2-q1]Gamma[P+1/2+q1]Gamma[P+1/2-q2]Gamma[P+1/2+q2]]]
bdyGHP[P_,q1_,q2_]:=
-{4 P Log[1+Exp[-x]]+CGHP[P,q1,q2](1-Tanh[x/2]),2P Log[1+Exp[-2x]]+CGHP[P,q1,q2](1-Tanh[x])}


(* ::Subsubsection:: *)
(*Q function*)


ClearAll[solGHP]
solGHP[PP_,qq1_,qq2_]:=solGHP[PP,qq1,qq2]=
ThermodynamicBetheAnsatzSolve[
tbaGHP/.{P->PP,q1->qq1,q2->qq2},
"BoundaryCondition"->bdyGHP[PP,qq1,qq2],"GridResolution"->2^12,"MonitorIterations"->True,"GridCutoff"->250,"StoppingAccuracy"->10^(-16),MaxIterations->8000]
ClearAll[lQ]
lQ[\[Theta]_,P_,q1_,q2_,K___:30(*,opts:OptionsPattern[solGHP]*)]/;NumericQ[K]:=
	Block[{sol},
sol=solGHP[P,q1,q2(*,opts*)];
-(4Sqrt[\[Pi]^3])/Gamma[1/4]^2 Exp[\[Theta]]-(\[Theta]+Log[2]/2)(q1+q2)+
1/(2*2\[Pi]) NIntegrate[1/Cosh[\[Theta]-y]
(Log[(1+Exp[-y3[y]])(1+Exp[-y2[y]])]
-I Exp[y-\[Theta]]Log[(1+Exp[-y3[y]])/(1+Exp[-y2[y]])])/.sol[[1]],{y,-K,K}]]//Chop


(* ::Subsection:: *)
(*Execution*)


core[P_,q1_,q2_]:=Block[{res,time,grid},
Echo[{P,q1,q2},"parameters:"];
time=AbsoluteTime[];
res=NumberForm[lQ[-1,P,q1,q2,50],16];
time=AbsoluteTime[]-time//Round[#,0.01]&//EchoLabel["time:"];
Echo[res,"result:"];
grid=ToString@Grid[{{"{\[Theta],P,q1,q2}:",N@{-1,P,q1,q2}},{"result",res},{"total time:",time}}];
(*SendMail[<|
|>]*)]


interactive:=Block[{\[Theta],P,q1,q2,res,time,grid},
\[Theta]=Input["enter \[Theta]: "];
P=Input["enter P: "];
q1=Input["enter q1: "];
q2=Input["enter q2: "];
Echo[{P,q1,q2},"parameters:"];
time=AbsoluteTime[];
res=NumberForm[lQ[\[Theta],P,q1,q2,50],16];
time=AbsoluteTime[]-time//Round[#,0.01]&//EchoLabel["time:"];
Echo[res,"result:"];
grid=ToString@Grid[{{"{\[Theta],P,q1,q2}:",N@{\[Theta],P,q1,q2}},{"result",res},{"total time:",time}}];
(*SendMail[<|
|>]*)];


table:=Table[core[Sequence@@Pq1q2],{Pq1q2,{{1.2,0.25,0.25},{1.2,1/4,1/8},{1.8,1/4,1/4},{1.8,1/3,1/6},{2.4,1/5,1/5},{2.4,1/5,1/4},{3.,1/4,1/4},{3.,1/4,1/8}}}]


(* ::Section:: *)
(*Run*)


If[MemberQ[$ScriptCommandLine,"interactive"],interactive,table]
