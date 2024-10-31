IntGL[expr_,lBounds__,OptionsPattern[{NbPoints->10,WorkingPrecision->MachinePrecision}]]:=Module[{nbVars,var,lBound,uBound,\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi],m,\[CapitalLambda],lRootsLegendre,lx,lw,u,k,j},
nbVars=Length[{lBounds}];
Do[Switch[Length[{lBounds}[[k]]],
3,var[k]={lBounds}[[k,1]];lBound[k]={lBounds}[[k,2]];uBound[k]={lBounds}[[k,3]];\[CurlyPhi][k]=Identity;inv\[CurlyPhi][k]=Identity;d\[CurlyPhi][k]=(1&),
4,var[k]={lBounds}[[k,1]];lBound[k]={lBounds}[[k,2]];uBound[k]={lBounds}[[k,3]];\[CurlyPhi][k]={lBounds}[[k,4,1]];inv\[CurlyPhi][k]={lBounds}[[k,4,2]];d\[CurlyPhi][k]={lBounds}[[k,4,3]],
_,Print["Error in IntGL: incorrect iterator"]
],{k,1,nbVars}];
m=OptionValue[NbPoints];
\[CapitalLambda]=OptionValue[WorkingPrecision];
lRootsLegendre=NSolve[LegendreP[m,u]==0,u,WorkingPrecision->\[CapitalLambda]];
Do[lx[k]=((inv\[CurlyPhi][k][uBound[k]]+inv\[CurlyPhi][k][lBound[k]])/2+(inv\[CurlyPhi][k][uBound[k]]-inv\[CurlyPhi][k][lBound[k]])/2u/.lRootsLegendre),{k,1,nbVars}];
Do[lw[k]=Map[d\[CurlyPhi][k],lx[k]]((inv\[CurlyPhi][k][uBound[k]]-inv\[CurlyPhi][k][lBound[k]])/(m LegendreP[m-1,u]D[LegendreP[m,u],u])/.lRootsLegendre),{k,1,nbVars}];
Sum[Product[lw[k][[j[k]]],{k,1,nbVars}](expr/.Table[var[k]->\[CurlyPhi][k][lx[k][[j[k]]]],{k,1,nbVars}]),Evaluate[Sequence@@Table[{j[k],1,m},{k,1,nbVars}]]]
];

FredholmDetGL[K_Function,{lBound_,uBound_,l\[CurlyPhi]_:{Identity,Identity,1&}},OptionsPattern[{NbPoints->10,WorkingPrecision->MachinePrecision}]]:=Module[{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi],m,\[CapitalLambda],lRootsLegendre,lx,lw,u,i,j},
\[CurlyPhi]=l\[CurlyPhi][[1]];
inv\[CurlyPhi]=l\[CurlyPhi][[2]];
d\[CurlyPhi]=l\[CurlyPhi][[3]];
m=OptionValue[NbPoints];
\[CapitalLambda]=OptionValue[WorkingPrecision];
lRootsLegendre=NSolve[LegendreP[m,u]==0,u,WorkingPrecision->\[CapitalLambda]];
lx=((inv\[CurlyPhi][uBound]+inv\[CurlyPhi][lBound])/2+(inv\[CurlyPhi][uBound]-inv\[CurlyPhi][lBound])/2u/.lRootsLegendre);
lw=Map[d\[CurlyPhi],lx]((inv\[CurlyPhi][uBound]-inv\[CurlyPhi][lBound])/(m LegendreP[m-1,u]D[LegendreP[m,u],u])/.lRootsLegendre);
Det[N[Table[KroneckerDelta[i,j]+Sqrt[lw[[i]]lw[[j]]]K[\[CurlyPhi][lx[[i]]],\[CurlyPhi][lx[[j]]]],{i,1,m},{j,1,m}],\[CapitalLambda]]]];

ReleaseHold[ReleaseHold[Hold[Hold[Module[{time,file,laDet,lStop,a,det},
file="/home/prolhac/sunos/Calculations/Fredholm/F2taMachinePrecision2/F2ta_t"<>ToString[N[t]]<>"_nbPts"<>ToString[nbPts]<>"_delta"<>ToString[N[\[Delta]a]]<>"_"<>DateString[{"Year",".","Month",".","Day",".","Hour",".","Minute",".","Second"}]<>".dat";
Print[file];
Put[file];
laDet={};
lStop={False,False,False,False,False};
a=0;
While[Not[And@@lStop],
det=FredholmDetGL[(-B[#1,#2]+P[#1,#2])&,{a,\[Infinity],{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi]}},NbPoints->nbPts,WorkingPrecision->precision]-FredholmDetGL[(-B[#1,#2])&,{a,\[Infinity],{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi]}},NbPoints->nbPts,WorkingPrecision->precision];
laDet=Append[laDet,{a,det}];
Print[TimeUsed[],"   a=",N[a],"   det=",det];
a=a+\[Delta]a;
lStop=Prepend[Delete[lStop,-1],Abs[det]<detMin];
];
lStop={False,False,False,False,False};
a=-\[Delta]a;
While[Not[And@@lStop],
det=FredholmDetGL[(-B[#1,#2]+P[#1,#2])&,{a,\[Infinity],{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi]}},NbPoints->nbPts,WorkingPrecision->precision]-FredholmDetGL[(-B[#1,#2])&,{a,\[Infinity],{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi]}},NbPoints->nbPts,WorkingPrecision->precision];
laDet=Prepend[laDet,{a,det}];
Print[TimeUsed[],"   a=",N[a],"   det=",det];
a=a-\[Delta]a;
lStop=Prepend[Delete[lStop,-1],Abs[det]<detMin];
];
Put[laDet,file]];]/.B->(IntGL[(AiryAi[#1+\[Lambda]]AiryAi[#2+\[Lambda]])/(1-E^(-\[Gamma]*\[Lambda]))+(AiryAi[#1-\[Lambda]]AiryAi[#2-\[Lambda]])/(1-E^(\[Gamma]*\[Lambda])),{\[Lambda],0,\[Infinity],{\[CurlyPhi],inv\[CurlyPhi],d\[CurlyPhi]}},NbPoints->nbPts,WorkingPrecision->precision]&)/.P->(AiryAi[#1]AiryAi[#2]&)/.\[CurlyPhi]->(10Tan[(\[Pi] #)/2]&)/.inv\[CurlyPhi]->(2/\[Pi]*ArcTan[#/10]&)/.d\[CurlyPhi]->((5 \[Pi])/Cos[(\[Pi] #)/2]^2&)]/.nbPts->30/.precision->MachinePrecision/.\[Delta]a->1/20/.detMin->10^(-5)/.\[Gamma]->(t/2)^(1/3)/.t->35/100]]
