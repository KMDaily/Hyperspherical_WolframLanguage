(* ::Package:: *)

(* Wolfram Language Package *)
(* :Title: Hyperspherical.m -- additional hyperspherical coordinate support *)

(* :Context: Hyperspherical` *)

(* :Author: Kevin M. Daily *)

(* :Summary:
   A translation into the Wolfram Language of Chapter 6 of Classical Orthogonal Polynomials of a Discrete Variable
By Arnold F. Nikiforov, Sergei K. Suslov, Vasilii B. Uvarov.
This does not include the unitary transformation coefficients.
 *)

(* :Package Version: 1.0  *)

(* :Mathematica Version: 10+ *)

(* :History:
   1.0 first released version.
*)

(* Created by the Wolfram Workbench Apr 14, 2017 *)
CoordinateChartData; Unprotect[CoordinateChartData];


BeginPackage["Hyperspherical`", {"GeneralUtilities`"}]
(* Exported symbols added here with SymbolName::usage *) 

SetUsage[BinaryTreeGraphQ, "BinaryTreeGraphQ[g$] yields True if the graph g$ is a binary tree graph and False otherwise."]
SetUsage[HypersphericalTreeGraphQ, "HypersphericalTreeQ[g$] yields True if the graph g$ follows the requirements for a hyperspherical coordinate tree and False otherwise."]
SetUsage[HypersphericalTreeGraph, "HypersphericalTreeGraph[n$] creates a canonical hyperspherical tree graph with n$ degrees of freedom.\nHypersphericalTreeGraph[{b$1,b$2,$$}] yields a hyperspherical tree graph using binary edges b$i."]
SetUsage[HypersphericalTreeSameQ, "HypersphericalTreeSameQ[g$1,g$2] yields True if the hyperspherical tree graphs g$1 and g$2 are morphologically equivalent."]
SetUsage[HypersphericalHarmonicY, "HypersphericalHarmonicY[{q$1,q$2,$$},{v$1,v$2,$$},g$] gives the hyperspherical harmonic with angular momenta q$, variables v$, and hyperspherical tree graph g$."]
SetUsage[iL, "iL is the head used to indicate a left-branching vertex in a hyperspherical graph."]
SetUsage[iR, "iR is the head used to indicate a right-branching vertex in a hyperspherical graph."]
SetUsage[iRoot, "iRoot is the head used to indicate the root vertex in a hyperspherical graph."]

Begin["`Private`"]
(* Implementation of the package *)

(* ::Section::Closed:: *)
(*BinaryTreeGraphQ*)


(*A binary tree is at least a tree, so must pass that test (no self loops or multiple paths between vertices.)*)
(*We make a choice that the tree is fully directed from root to leaves.*)
(*Because of these 2 choices, the only thing left to check is that each node has either 0 or 2 branches.*)
BinaryTreeGraphQ[g_?(TreeGraphQ[#] && DirectedGraphQ[#]&)] := MatchQ[VertexOutDegree[g], {(0|2)...}]
BinaryTreeGraphQ[g_] := False
SyntaxInformation[BinaryTreeGraphQ] = {"ArgumentsPattern" -> {_}};

(* ::Section::Closed:: *)
(*Binary tree property functions*)


(*find the root vertex of a binary tree graph*)
findBinaryTreeRoot[g_?BinaryTreeGraphQ] := Pick[VertexList[g], VertexInDegree[g], 0][[1]]


(*find the leaves of a binary tree graph*)
(*the list of vertices are not guaranteed to be ordered w.r.t. a hyperspherical tree ordering*)
findBinaryTreeLeaves[g_?BinaryTreeGraphQ] := Pick[VertexList[g], VertexOutDegree[g], 0]


(*find all paths in the binary tree from the root to the leaves*)
findBinaryTreePaths[g_?BinaryTreeGraphQ] := FindPath[g, findBinaryTreeRoot[g], #][[1]]& /@ findBinaryTreeLeaves[g]


(* ::Section::Closed:: *)
(*HypersphericalTreeGraphQ*)


(*check that all branching vertices contain one left (iL[_]) and one right (iR[_]) branch*)
(*check that there is only one root (iRoot[_])*)
HypersphericalTreeGraphQ[g_?BinaryTreeGraphQ /; EdgeList[g]=={}] := MatchQ[VertexList[g],{iRoot[_]}] 

HypersphericalTreeGraphQ[g_?BinaryTreeGraphQ] := With[{edgeList=GatherBy[EdgeList[g],First]},
	(*'edgeList' holds all edge pairs of the binary tree, grouped by root*)
	
	(*check that each binary pair's leaves are exactly 1 iL and 1 iR*)
	MatchQ[edgeList[[All,All,2]],{({iL[_],iR[_]}|{iR[_],iL[_]})...}] && 
	
	(*check that only one vertex is iRoot*)
	Count[edgeList[[All,1,1]], iRoot[_]] == 1 
]
HypersphericalTreeGraphQ[_] := False
SyntaxInformation[HypersphericalTreeGraphQ] = {"ArgumentsPattern" -> {_}}

(* ::Section::Closed:: *)
(*Hyperspherical tree property functions*)


(* ::Text:: *)
(*These functions return lists of vertices or vertex indices, ordered w.r.t. the classical hyperspherical tree layout.*)


(*return all ordered paths in the hyperspherical tree from the root to the leaves*)
(*a fractal approach is taken, based on each unordered branch path*)
findOrderedBinaryTreePaths[g_?HypersphericalTreeGraphQ] := With[{bps = findBinaryTreePaths[g]},
	bps[[Ordering@Apply[Plus, (bps /. {iRoot[_] -> 0, iL[_] -> -1, iR[_] -> 1})*(2^-Range[0,Length[#]-1]& /@ bps), {1}]]]
]


(*find the ordered positions in VertexList where the leaves of the hyperspherical tree appear*)
findOrderedLeafIndices[g_?HypersphericalTreeGraphQ] := Flatten[Position[VertexList[g],#]& /@ findOrderedBinaryTreePaths[g][[All,-1]],2]

(*find the tree graph leaves in order from left to right*)
findOrderedBinaryTreeLeaves[g_?HypersphericalTreeGraphQ] := findOrderedBinaryTreePaths[g][[All, -1]]


(*compare two hyperspherical graphs for equality*)
(*only heads iL, iR, and iRoot are compared*)
(*findOrderedBinaryTreePaths[g][[All,All,0]] can be thought of as the fingerprint of the hyperspherical tree graph*)
HypersphericalTreeSameQ[g1_?HypersphericalTreeGraphQ, g2_?HypersphericalTreeGraphQ] := SameQ[findOrderedBinaryTreePaths[g1][[All,All,0]], findOrderedBinaryTreePaths[g2][[All,All,0]]]
SyntaxInformation[HypersphericalTreeSameQ] = {"ArgumentsPattern" -> {_,_}}

(* ::Section::Closed:: *)
(*HypersphericalTreeGraph[n] (integer argument)*)


(* ::Subsection::Closed:: *)
(*vertexCoordinateRules (finds hyperspherical vertex coordinates as rules)*)


(*creates rules where vertices should be placed; each edge has the same slope, based on width*)
vertexCoordinateRules[g_?HypersphericalTreeGraphQ, width_?NumericQ] := Module[{bps, assoc, t, m, graphCoordinateRules},
	(*start with vertices, grouped by full branch, and branch groups ordered by hyperspherical leaf ordering*)
	bps = findOrderedBinaryTreePaths[g];
		
	(*create list of association of branching vertex as key, and {left,right} branches as values*)
	(*there's probably a better way to do this as the algorithm is rather logical*)
	assoc={};
	Do[
		t=Select[bps, Length[#]==i&];
		AppendTo[assoc, Map[Last, GroupBy[t,#[[-2]]&], {2}]];
		bps = DeleteDuplicates[Take[#,UpTo[i-1]]& /@ bps];
		,{i, Max[Length /@ bps], 2, -1}
	];
	
	(*initialize first row of hyperspherical tree*)
	graphCoordinateRules = With[{l=VertexList[g][[findOrderedLeafIndices[g]]]}, Thread[l -> Table[{i,0},{i,Length[l]}]] ];
	(*recursively create subsequent levels, down to the root. 'Normal' converts Association to rules.*)
	Do[graphCoordinateRules = Join[graphCoordinateRules, 
		Normal@ Map[
				{-((-m #1[[1,1]]-#1[[1,2]]-m #1[[2,1]]+#1[[2,2]])/(2 m)),1/2 (m #1[[1,1]]+#1[[1,2]]-m #1[[2,1]]+#1[[2,2]])} /. m -> width &, 
				assoc[[i]] /. graphCoordinateRules
			]
		]
		,{i,1,Length[assoc],1}
	];
	graphCoordinateRules
]


(* ::Subsection::Closed:: *)
(*updateVertexCoordinates*)


(*update the vertex coordinate property of a graph*)
(*there's an issue with changing the VertexCoordintes property of a graph;
if the Property has not been changed, then you can update all of them at once,
if the Property has already been changed, then you need to update one vertex at a time*)
Attributes[updateVertexCoordinates]={HoldFirst};
updateVertexCoordinates[g_?GraphQ, coordinateList:{{_?NumericQ,_?NumericQ}..}] := If[PropertyValue[g,VertexCoordinates]===Automatic,
	If[Length[VertexList[g]]==Length[coordinateList], 
		PropertyValue[g,VertexCoordinates] = coordinateList,
		Message[Set::pvw, Defer[PropertyValue[g,VertexCoordinates]]]
	],
	MapThread[(PropertyValue[{g,#1},VertexCoordinates]=#2)&, {VertexList[g], coordinateList}]
]


(* ::Subsection::Closed:: *)
(*renumberVertices (root=1, leaves are last) using replacement rules*)
(*in truth, all that matters are the heads iL, iR, and iRoot and their arguments are unimportant*)


renumberVertices[g_?HypersphericalTreeGraphQ, n_Integer:0] := Module[{reps, oldVerts, newVerts, oldLeaves, newLeaves, bps},
	bps = findOrderedBinaryTreePaths[g];
	oldVerts = DeleteDuplicates[Join@@ bps[[All,;;-2]]];
	newVerts = Inner[#2@#1&, n+Range[Length[oldVerts]], Head /@ oldVerts, List, 1];
	oldLeaves = bps[[All,-1]];
	newLeaves = Inner[#2@#1&, n+Range[Length[newVerts]+1, Length[newVerts]+1+Length[oldVerts]], Head /@ oldLeaves, List, 1];
	reps = Join[ Thread[oldVerts -> newVerts], Thread[oldLeaves -> newLeaves] ];
	Graph[VertexList[g] /. reps, EdgeList[g] /. reps]
]


(* ::Subsection::Closed:: *)
(*main (creates canonical tree with n leaves)*)


Attributes[HypersphericalTreeGraph] = {HoldAll};
HypersphericalTreeGraph::canonical="The degrees of freedom `1` is not a positive integer.";

(*treat 1 and 2 vertex graphs as special cases*)
HypersphericalTreeGraph[n_Integer /; n < 1] := (Message[HypersphericalTreeGraph::canonical,n];Defer[HypersphericalTreeGraph[n]])
HypersphericalTreeGraph[1, opts:OptionsPattern[]] := Graph[{iRoot[1]}, {}]
HypersphericalTreeGraph[2, opts:OptionsPattern[]] := Module[{g},
	g = Graph[{iRoot[3], iL[1], iR[2]}, {iRoot[3]\[DirectedEdge]iL[1],iRoot[3]\[DirectedEdge]iR[2]}, VertexCoordinates->{{3/2,-1/2},{1,0},{2,0}}];
	g = renumberVertices[g];
	updateVertexCoordinates[g, VertexList[g] /. vertexCoordinateRules[g, 1]];
	Switch[OptionValue[VertexLabels],
		"Angles",   Graph[g, VertexLabels -> getAngularVertexLabels[g], opts],
		"Ordering", Graph[g, VertexLabels -> getOrderedVertexLabels[g], opts],
		_, Graph[g, VertexLabels -> OptionValue[VertexLabels], opts]
	]
]
HypersphericalTreeGraph[n_Integer /; n > 2, opts:OptionsPattern[]] := Module[{g, edges},
	edges = Thread[Flatten@Join[{1,1},Table[{2 i,2 i},{i,1,n-2}]] -> Range[2,2 n-1]] /. {1 -> iRoot[1], x_?EvenQ :> iL[x], x_?OddQ :> iR[x]};
	g = Graph[edges];
	g = renumberVertices[g];
	updateVertexCoordinates[g, VertexList[g] /. vertexCoordinateRules[g,1] ];
	Switch[OptionValue[VertexLabels],
		"Angles",   Graph[g, VertexLabels -> getAngularVertexLabels[g], opts],
		"Ordering", Graph[g, VertexLabels -> getOrderedVertexLabels[g], opts],
		_, Graph[g, VertexLabels -> OptionValue[VertexLabels], opts]
	]
]
SyntaxInformation[HypersphericalTreeGraph] = {"ArgumentsPattern" -> {_,OptionsPattern[]}}

(* ::Section::Closed:: *)
(*HypersphericalTreeGraph[{1\[DirectedEdge]{2,3}, g[A,n]\[DirectedEdge]{g[B],g[C]}, ...}]*)

(*The syntax for a hyperspherical tree graph is a list directed edges:
+ each vertex source can be 
  - an expression
  - a hyperspherical tree graph g as the head with a unique dummy argument e.g. g[A]
  - a hyperspherical tree graph g as the head with a unique dummy argument and leaf index e.g. g[A,1]
+ the vertex source can point to
  - a pair of expressions that represent other ordered vertices e.g. {2,3} implies {iL[2],iR[3]}
  - a pair of hyperspherical tree graphs with dummy arguments as labels e.g. {g[A],g[A]}
  - a single hyperspherical tree graph with dummy argument as label e.g. g[A,1] -> g[A]
  
If the source points to a graph, the graph's root replaces the source.
For example, g[A,1] -> g[A] implies that the 1st leaf of g becomes a graph of the same shape as g[A].
Labels are used to avoid ambiguity, but serve no other purpose and are removed in the final expression.
g[A] -> g[B] is a special case that replaces all leaves of g[A] with the tree g[B].
*)


(* ::Subsection::Closed:: *)
(*hstg (accepted edge forms)*)


(* ::Subsubsection::Closed:: *)
(*findAndConvert (converts vertex source graph to appropriate graph-vertex)*)


findAndConvert[g1_, gList_] := Select[gList, HypersphericalTreeSameQ[#[[0]], g1[[0]]] && #[[1]]==g1[[1]] &][[1,0]]


(* ::Subsubsection::Closed:: *)
(*g[A, n] \[DirectedEdge] {g[B], g[C]}*)


hstg[(Rule|DirectedEdge)[g1_Graph[s1_,z_Integer], {g2_Graph[s2_], g3_Graph[s3_]}], gList_] := Module[{leaf, el2, el3},
	(*get edge lists from graph-vertices g2 and g3, and leaf from g1*)
	leaf = VertexList[findAndConvert[g1[s1], gList]][[findOrderedLeafIndices[g1][[z]]]];
	el2 = EdgeList[g2];
	el3 = EdgeList[g3];
	
	(*flatten all rules*)
	Flatten@ 
	{leaf \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iL[A]],
	leaf \[DirectedEdge] FirstCase[el3, (Rule|DirectedEdge)[iRoot[A_], _] :> iR[A]],
	el2 /. iRoot[A_] :> iL[A],
	el3 /. iRoot[A_] :> iR[A]}
]


(* ::Subsubsection::Closed:: *)
(*g[A, n] \[DirectedEdge] {g[B], v1}*)


hstg[(Rule|DirectedEdge)[g1_Graph[s1_,z_Integer], {g2_Graph[s2_], v_}], gList_] := Module[{leaf, el2},
	(*get edge lists from graph-vertices g2 and leaf from g1*)
	leaf = VertexList[findAndConvert[g1[s1], gList]][[findOrderedLeafIndices[g1][[z]]]];
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	Flatten@ 
	{leaf \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iL[A]],
	leaf \[DirectedEdge] v,
	el2 /. iRoot[A_] :> iL[A]}
]


(* ::Subsubsection::Closed:: *)
(*g[A, n] \[DirectedEdge] {v1, g[B]}*)


hstg[(Rule|DirectedEdge)[g1_Graph[s1_,z_Integer], {v_, g2_Graph[s2_]}], gList_] := Module[{leaf, el2},
	(*get edge lists from graph-vertices g2 and leaf from g1*)
	leaf = VertexList[findAndConvert[g1[s1], gList]][[findOrderedLeafIndices[g1][[z]]]];
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	Flatten@ 
	{leaf \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iR[A]],
	leaf \[DirectedEdge] v,
	el2 /. iRoot[A_] :> iR[A]}
]


(* ::Subsubsection::Closed:: *)
(*g[A, n] \[DirectedEdge] {v1, v2}*)


hstg[(Rule|DirectedEdge)[g1_Graph[s1_,z_Integer], {v1_, v2_}], gList_] := Module[{leaf},
	(*get leaf from g1*)
	leaf = VertexList[findAndConvert[g1[s1], gList]][[findOrderedLeafIndices[g1][[z]]]];
	
	(*flatten all rules*)
	{leaf \[DirectedEdge] v1, leaf \[DirectedEdge] v2}
]


(* ::Subsubsection::Closed:: *)
(*g[A, n] \[DirectedEdge] g[B] (special case of leaf replacement)*)


hstg[(Rule|DirectedEdge)[g1_Graph[s1_,z_Integer], g2_Graph[s2_]], gList_] := Module[{leaf, el2},
	(*get edge lists from graph-vertices g2 and leaf from g1*)
	leaf = VertexList[findAndConvert[g1[s1], gList]][[findOrderedLeafIndices[g1][[z]]]];
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	el2 /. iRoot[_] :> leaf
]


(* ::Subsubsection::Closed:: *)
(*v1 \[DirectedEdge] {g[B], g[C]}*)


hstg[(Rule|DirectedEdge)[v_, {g2_Graph[s2_], g3_Graph[s3_]}], gList_] := Module[{el2, el3},
	(*get edge lists from graph-vertices g2 and g3*)
	el2 = EdgeList[g2];
	el3 = EdgeList[g3];
	
	(*flatten all rules*)
	Flatten@ 
	{v \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iL[A]],
	v \[DirectedEdge] FirstCase[el3, (Rule|DirectedEdge)[iRoot[A_], _] :> iR[A]],
	el2 /. iRoot[A_] :> iL[A],
	el3 /. iRoot[A_] :> iR[A]}
]


(* ::Subsubsection::Closed:: *)
(*v1 \[DirectedEdge] {g[B], v2}*)


hstg[(Rule|DirectedEdge)[v1_, {g2_Graph[s2_], v2_}], gList_] := Module[{el2},
	(*get edge list from graph-vertices g2*)
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	Flatten@ 
	{v1 \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iL[A]],
	v1 \[DirectedEdge] v2,
	el2 /. iRoot[A_] :> iL[A]}
]


(* ::Subsubsection::Closed:: *)
(*v1 \[DirectedEdge] {v2, g[B]}*)


hstg[(Rule|DirectedEdge)[v1_, {v2_, g2_Graph[s2_]}], gList_] := Module[{el2},
	(*get edge list from graph-vertices g2*)
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	Flatten@ 
	{v1 \[DirectedEdge] v2,
	v1 \[DirectedEdge] FirstCase[el2, (Rule|DirectedEdge)[iRoot[A_], _] :> iR[A]],
	el2 /. iRoot[A_] :> iR[A]}
]


(* ::Subsubsection::Closed:: *)
(*v1 \[DirectedEdge] {v2, v3}*)


hstg[(Rule|DirectedEdge)[v1_, {v2_, v3_}], gList_] := {v1 \[DirectedEdge] v2, v1 \[DirectedEdge] v3}


(* ::Subsubsection::Closed:: *)
(*v1 \[DirectedEdge] g[B] (special case)*)


hstg[(Rule|DirectedEdge)[v1_, g2_Graph[s2_]], gList_] := Module[{el2},
	(*get edge list from graph-vertices g2*)
	el2 = EdgeList[g2];
	
	(*flatten all rules*)
	el2 /. iRoot[A_] :> v1
]


(* ::Subsection::Closed:: *)
(*argument checks*)


(* ::Subsubsection::Closed:: *)
(*hypersphericalTreeVerticesQ (check that all graph-vertices are of hyperspherical type)*)


HypersphericalTreeGraph::graphAsVertexError1="The graph `1` does not appear at the head e.g. g[A,1] or g[A].";
HypersphericalTreeGraph::graphAsVertexError2="The graph `1` is not a hyperspherical tree graph.";
hypersphericalTreeVerticesQ[input_List] := Module[{p, res=True},
	(*check that graphs only appear as the head of an expression*)
	p = Cases[input, _Graph, Infinity];
	Message[HypersphericalTreeGraph::graphAsVertexError1, #]& /@ p;
	If[Length[p] > 0, res=False];
	
	p = Cases[input, _Graph, Infinity, Heads -> True];
	If[!HypersphericalTreeGraph[#], Message[HypersphericalTreeGraph::graphAsVertexError2, #]; res=False]& /@ p;
	res
]


(* ::Subsubsection::Closed:: *)
(*hypersphericalLeavesExistQ (check that branches come from existing leaves)*)


HypersphericalTreeGraph::leafExistQ="Leaf `1` of graph `2` does not exist.";
hypersphericalLeavesExistQ[input_List] := Module[{leaves, res},
	leaves = Cases[input, (Rule|DirectedEdge)[x_Graph[y_, z_Integer], _] :> {x,z}];
	res = If[#[[2]] > Length[findBinaryTreeLeaves[#[[1]]]], Message[HypersphericalTreeGraph::leafExistQ,#[[2]],#[[1]]]; False, True]& /@ leaves;
	And@@ res
]


(* ::Subsection::Closed:: *)
(*other helper functions*)


(* ::Subsubsection::Closed:: *)
(*positionDuplicates*)


positionDuplicates[list_] := GatherBy[Range@Length[list], list[[#]]&]

(*generate list of rules of vertices with their standard coordinate names*)
getAngularVertexLabels[g_?HypersphericalTreeGraphQ] := With[{vars=CoordinateChartData[{"Hyperspherical", "Euclidean", g}, "StandardCoordinateNames"] /. x_String :> ToExpression[x]},
  Thread[SortBy[Cases[VertexList[g], _[x_] /; x <= Length[vars] - 1], First] -> Table[Tooltip[vars[[i]],i-1],{i,2,Length[vars]}]]
]

(*generate list of rules of vertices with their ordering in the graph*)
getOrderedVertexLabels[g_?HypersphericalTreeGraphQ] := With[{vars=CoordinateChartData[{"Hyperspherical", "Euclidean", g}, "StandardCoordinateNames"] /. x_String :> ToExpression[x]},
  Thread[SortBy[Cases[VertexList[g], _[x_] /; x <= Length[vars] - 1], First] -> Range[1, Length[vars]-1]]
]

(* ::Subsection::Closed:: *)
(*main*)


HypersphericalTreeGraph::inputSyntaxError="One of the inputs is not of the accepted format _ \[Rule] {_,_} or _ \[Rule] _Graph.";
HypersphericalTreeGraph::inputDisconnected="Input leads to a graph that is disconnected.";
HypersphericalTreeGraph::duplicatedRoot="Input contains a duplicated root at position `1`.";
HypersphericalTreeGraph::duplicatedLeaf="Input contains a duplicated root at position `1`.";

Options[HypersphericalTreeGraph] = Join[{VertexLabels -> None}, Options[Graph]]

HypersphericalTreeGraph[input_?ListQ, opts:OptionsPattern[Graph]] := Module[
{edges, graphs, g, graphRoot, reps, check, check2, v, u2, duplicateLeaves, duplicateRoots, graphVertices},
	(*if all input graph-vertices are hyperspherical, then expand any special syntax graph1 \[Rule] graph2*)
	If[!hypersphericalTreeVerticesQ[input], Return[Defer[HypersphericalTreeGraph[input]]]];
	edges = input /. (DirectedEdge|Rule)[x_Graph[z_], y_Graph[_]] :> Sequence@@ Table[DirectedEdge[x[z,i], y[Unique[v]]], {i, Length[findBinaryTreeLeaves[x]]}];
	
	(*check that input syntax is correct, _\[Rule]{_,_} or _\[Rule]_Graph[_]*)
	If[!MatchQ[edges, {((Rule|DirectedEdge)[_, {_, _}] | (Rule|DirectedEdge)[_, _Graph[_]])...}],
		Message[HypersphericalTreeGraph::inputSyntaxError]; 
		Defer[HypersphericalTreeGraph[input]]
	];
		
	(*check that all requested leaves exist*)
	If[!hypersphericalLeavesExistQ[edges], Return[Defer[HypersphericalTreeGraph[input]]]];
			
	(*check that the resulting graph is connected*)
	(*get all graphs from the input*)
	graphs = Extract[edges, Position[edges, _Graph]];
	
	(*replace all equivalent graphs with the same unique symbol*)
	reps = With[{u=DeleteDuplicates[graphs, HypersphericalTreeSameQ]},
		MapThread[x_Graph /; HypersphericalTreeSameQ[#1,x] :> #2&, {u, Array[v,Length[u]]}]
	];
	check = edges /. reps;
	
	(*check for duplicated roots or leaves*)
	duplicateRoots = Select[positionDuplicates[check[[All,1]]], Length[#] > 1 &];
	Message[HypersphericalTreeGraph::duplicatedRoot, #]& /@ duplicateRoots;
	If[Length[duplicateRoots] > 0, Return[Defer[HypersphericalTreeGraph[input]]]];
	
	duplicateLeaves = Select[positionDuplicates[Flatten@ check[[All,2]]], Length[#] > 1 &];
	Message[HypersphericalTreeGraph::duplicatedLeaf, #]& /@ duplicateLeaves;
	If[Length[duplicateLeaves] > 0, Return[Defer[HypersphericalTreeGraph[input]]]];
	
	(*check that the graph is a weakly connected tree graph*)
	(*remove integer index of graph-vertex leaves; flatten out branch pairs*)
	check2 = check /. {
		(Rule|DirectedEdge)[x_[y_, _Integer], {z_,w_}] :> Sequence[x[y]\[DirectedEdge]z, x[y]\[DirectedEdge]w],
		(Rule|DirectedEdge)[x_[y_, _Integer], z_] :> x[y]\[DirectedEdge]z,
		(Rule|DirectedEdge)[x_, {y_, z_}] :> Sequence[x\[DirectedEdge]y, x\[DirectedEdge]z]};
		
	(*confirm that result is a tree graph*)
	If[!TreeGraphQ[Graph[check2]], 
		Message[HypersphericalTreeGraph::inputDisconnected];
		Return[Return[Defer[HypersphericalTreeGraph[input]]]]
	];
	
	(*==== PERFORM MAIN CALCULATION ====*)
	(*make each graph-vertex have unique inner vertices*)
	u2 = edges /. x_Graph :> With[{el=EdgeList[x], u=Unique[v]}, 
		Graph[el /. {iL[a_] :> iL[u[a]], iR[a_] :> iR[u[a]], iRoot[a_] :> iRoot[u[a]]}]
	];
	
	(*Extract graph-vertices, including those that may act as the main root*)
	graphVertices = Cases[u2[[All,2]], _Graph[_], 2];
	With[{gv2=DeleteDuplicates[Cases[u2[[All,1]],x_Graph[y_,z_Integer]:>x[y]],HypersphericalTreeSameQ[#1[[0]],#2[[0]]]&&#1[[1]]==#2[[1]]&]},
		graphRoot = Pick[gv2, !MemberQ[graphVertices, (x_Graph /; HypersphericalTreeSameQ[x,#[[0]]])[y_ /; y===#[[1]]]]& /@ gv2];
	];
	graphVertices = Join[graphVertices, graphRoot];
	
	(*Convert all non-graph-vertices to iL and iR versions*)
	reps = Flatten[Cases[u2,(Rule|DirectedEdge)[_,{a_,b_}] :> {
		If[MatchQ[a, _Graph[_]], {}, a->iL[a]], 
		If[MatchQ[b, _Graph[_]], {}, b->iR[b]]}]
	];
	
	u2 = Thread[Replace[u2[[All,1]],reps,{1}] \[DirectedEdge] Replace[u2[[All,2]],reps,{2}]];
	u2 = Flatten[hstg[#, graphVertices]& /@ u2];
	(*if a graph-vertex is the root, then add its edges, otherwise convert the remaining vertex to iRoot[vertex]*)
	u2 = If[Length[graphRoot]==1, 
		Join[u2, EdgeList[graphRoot[[1,0]]]],
		u2 = u2 /. DirectedEdge[x:Except[_iL|_iR],y_] :> iRoot[x]\[DirectedEdge]y
	];
	g = Graph[u2 /. DirectedEdge[x:Except[_iL|_iR],y_] :> iRoot[x]\[DirectedEdge]y];
	g = renumberVertices[g];
	updateVertexCoordinates[g, VertexList[g] /. vertexCoordinateRules[g, 1]];
	
	Switch[OptionValue[VertexLabels],
		"Angles",   Graph[g, VertexLabels -> getAngularVertexLabels[g], opts],
		"Ordering", Graph[g, VertexLabels -> getOrderedVertexLabels[g], opts],
		_, Graph[g, VertexLabels -> OptionValue[VertexLabels], opts]
	]
];

HypersphericalTreeGraph[g_?HypersphericalTreeGraphQ, opts:OptionsPattern[]] := Switch[OptionValue[VertexLabels],
	"Angles",   Graph[g, VertexLabels -> getAngularVertexLabels[g], opts],
	"Ordering", Graph[g, VertexLabels -> getOrderedVertexLabels[g], opts],
	_, Graph[g, VertexLabels -> OptionValue[VertexLabels], opts]
]

(* ::Section:: *)
(*CoordinateChartData*)


(* ::Subsection::Closed:: *)
(*unprotect downvalues*)


(*There is only one DownValue for CoordinateChartData, which we want to come last*)
odvCoordinateChartData = DownValues[CoordinateChartData][[-1]];
DownValues[CoordinateChartData] = {};


(* ::Subsection::Closed:: *)
(*new definitions for CoordinateChartData*)


CoordinateChartData[patt:{"Hyperspherical", "Euclidean", g_Graph?HypersphericalTreeGraphQ}
|{{"Hyperspherical",{}}, "Euclidean", g_Graph?HypersphericalTreeGraphQ}
|{"Hyperspherical", {"Euclidean",{}}, g_Graph?HypersphericalTreeGraphQ}
|{{"Hyperspherical",{}}, {"Euclidean",{}}, g_Graph?HypersphericalTreeGraphQ}, prop_String, vars_] := Module[{L=Length[findBinaryTreeLeaves[g]]},
	(*check that variables are a list*)
	If[Head[vars] =!= List, 
		Message[CoordinateChartData::list, Defer[CoordinateChartData[patt, prop, vars]], 3];
		Return@ Defer[CoordinateChartData[patt, prop, vars]]	
	];
	(*check that the number of variables agrees with the number of hyperspherical tree leaves*)
	If[Length[vars] =!= L, 
		Message[CoordinateChartData::dimp, vars, Length[vars], L];
		Return@ Defer[CoordinateChartData[patt, prop, vars]]
	];
	(*only accept the acceptable coordinate chart properties*)
	If[!MatchQ[prop, "TangentBasis"|"CotangentBasis"|"CoordinateRangeAssumptions"
		|"Dimension"|"InverseMetric"|"InverseMetricTensor"|"Metric"|"MetricTensor"
		|"LeviCivitaConnection"|"OrthonormalBasis"|"ParameterRangeAssumptions"
		|"Properties"|"RiemannTensor"|"RicciTensor"|"RicciScalar"|"ScaleFactors"
		|"VolumeFactor"|"AlternateCoordinateNames"|"StandardName"|"StandardCoordinateNames"
		|"FullName"|"StandardCoordinateSystem"],
		Message[CoordinateChartData::notprop,prop,CoordinateChartData];
		Return@ Defer[CoordinateChartData[patt, prop, vars]]
	];
	If[MatchQ[prop, "CoordinateRangeAssumptions"|"InverseMetric"|"InverseMetricTensor"
		|"LeviCivitaConnection"|"Metric"|"MetricTensor"|"OrthonormalBasis"|"ScaleFactors"
		|"VolumeFactor"],
		computeProp[g, prop][vars],
		computeProp[g, prop]
	]	
]


CoordinateChartData[patt:{"Hyperspherical", "Euclidean", g_Graph?HypersphericalTreeGraphQ}
|{{"Hyperspherical",{}}, "Euclidean", g_Graph?HypersphericalTreeGraphQ}
|{"Hyperspherical", {"Euclidean",{}}, g_Graph?HypersphericalTreeGraphQ}
|{{"Hyperspherical",{}}, {"Euclidean",{}}, g_Graph?HypersphericalTreeGraphQ}, prop_] := computeProp[g, prop]	


(* ::Subsection::Closed:: *)
(*Christoffel symbol*)


(*'met' is metric, 'imet' is inverse metric*)
chris[i_,k_,l_,met_,imet_,symbols_]:=Sum[1/2 imet[[i,m]]*(D[met[[m,k]],symbols[[l]]]+D[met[[m,l]],symbols[[k]]]-D[met[[k,l]],symbols[[m]]]),{m,Length[met]}]


(* ::Subsection:: *)
(*computeProp*)


(* ::Subsubsection::Closed:: *)
(*AlternateCoordinateNames*)


computeProp[g_Graph, "AlternateCoordinateNames"] := Missing["NotAvailable"]


(* ::Subsubsection:: *)
(*CoordinateRangeAssumptions*)


computeProp[g_Graph, "CoordinateRangeAssumptions"] := Module[{gb, res, l=Length[findBinaryTreeLeaves[g]]},
	If[l==1, Return[{0<#[[1]]}&]];
	If[l==2, Return[{0<#[[1]],0<#[[2]]<2\[Pi]}&]];
	
	(*gather pairs of edges by their roots*)
	gb = Sort /@ GatherBy[EdgeList[g], First];
	If[gb==={}, Return[{}]];
	
	(*count leaves from each edge pair*)
	gb = Rule@@@ (gb /. {DirectedEdge[x1_,y1_], DirectedEdge[x1_,y2_]} :> {x1, {VertexOutDegree[g,y1], VertexOutDegree[g,y2]}});
	
	(*based on ordered tree paths, order the leaf counts*)
	res = DeleteDuplicates@ Flatten@ findOrderedBinaryTreePaths[g][[All, ;;-2]] /. gb;
	
	(*index each leaf count, put within And*)
	res = And@@ Transpose[{1+ Range@ Length@ res, res[[All,1]], res[[All,2]]}];
	PrependTo[res, "R"];
	
	(*create pure functional form of coordinate range assumptions*)
	Hold[Evaluate[res]]/.{
		"R" :> 0 < #[[1]],
		{x_Integer,2,0} :> 0 < #[[x]] < \[Pi],
		{x_Integer,0,2} :> -\[Pi]/2 < #[[x]] < \[Pi]/2,
		{x_Integer,2,2} :> 0 < #[[x]] < \[Pi]/2,
		{x_Integer,0,0} :> 0 < #[[x]] < 2 \[Pi],
		Hold -> Function}
]


(* ::Subsubsection::Closed:: *)
(*Dimension*)


computeProp[g_Graph, "Dimension"] := Length[findBinaryTreeLeaves[g]]


(* ::Subsubsection::Closed:: *)
(*FullName*)


computeProp[g_Graph, "FullName"] := {{"Hyperspherical", {}}, {"Euclidean", {}}, g}


(* ::Subsubsection:: *)
(*InverseMetric*)


computeProp[g_Graph, "InverseMetric"] := Module[{bps, bps2, reps, verts},
	If[EdgeList[g]==={}, Return[{{1}}&]];
	
	(*shift heads of vertices in ordered paths to the left, remove the leaves (that now are wrapped in iRoot)*)
	bps = findOrderedBinaryTreePaths[g];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	
	(*make replacement rules to renumber vertex arguments from 2 to n*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All,All,1]]}, Thread[list -> 1+ Range@ Length@ list]];
	(*get original set of vertices (without the leaves)*)
	verts = DeleteDuplicates@ Flatten@ bps[[All,;;-2]];
	
	(*follow the path to each non-leaf vertex to define the metric via the Lam\[EAcute] factors; the heads are shifted left like was done above*)
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts],#][[1]]& /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	Hold[Evaluate[DiagonalMatrix[Join[{1,"R"}, "R"*(Times@@@ Rest[bps2] /. reps)]^-2]]] /. 
		{iL[n_Integer] :> Sin[#[[n]]], 
		iR[n_Integer] :> Cos[#[[n]]], 
		"R" :> #[[1]], 
		Hold->Function}
]


(* ::Subsubsection::Closed:: *)
(*InverseMetricTensor*)


computeProp[g_Graph, "InverseMetricTensor"] := Module[{bps, bps2, reps, verts, L},
	If[EdgeList[g]==={}, Return[{{1}}&]];
	
	(*shift heads of vertices in ordered paths to the left, remove the leaves (that now are wrapped in iRoot)*)
	bps = findOrderedBinaryTreePaths[g];
	L = Length[bps];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	
	(*make replacement rules to renumber vertex arguments from 2 to n*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All,All,1]]}, Thread[list -> 1+ Range@ Length@ list]];
	(*get original set of vertices (without the leaves)*)
	verts = DeleteDuplicates@ Flatten@ bps[[All,;;-2]];
	
	(*follow the path to each non-leaf vertex to define the metric via the Lam\[EAcute] factors; the heads are shifted left like was done above*)
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts],#][[1]]& /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	Hold[Evaluate[
		SymbolicTensors`Tensor[
			DiagonalMatrix[Join[{1,"R"}, "R"*(Times@@@ Rest[bps2] /. reps)]^-2],
			{
				SymbolicTensors`TangentBasis["head" /@ Range[L]],
				SymbolicTensors`TangentBasis["head" /@ Range[L]]
			}
		]
	]] /. { iL[n_Integer] :> Sin[#[[n]]], iR[n_Integer] :> Cos[#[[n]]], 
		"R" :> #[[1]], "head"[n_Integer] :> #[[n]], Hold->Function}
]


(* ::Subsubsection::Closed:: *)
(*LeviCivitaConnection*)


computeProp[g_Graph,"LeviCivitaConnection"] := Module[{x,symbols,met,imet,L},
	L = Length[findBinaryTreeLeaves[g]];
	symbols = Array[x, L];
	met=CoordinateChartData[{"Hyperspherical","Euclidean",g}, "Metric", symbols];
	imet=CoordinateChartData[{"Hyperspherical","Euclidean",g}, "InverseMetric", symbols];
	Hold[
		Evaluate@SymbolicTensors`Tensor[ 
			Table[chris[i,k,l,met,imet,symbols],{i,L},{k,L},{l,L}],
			{
				SymbolicTensors`TangentBasis[ symbols ],
				SymbolicTensors`CotangentBasis[ symbols ],
				SymbolicTensors`CotangentBasis[ symbols ]
			}
		]
	] /. Join[Table[With[{i=i}, symbols[[i]] :> #[[i]]], {i,Length[symbols]}], {Hold -> Function}]
]


(* ::Subsubsection::Closed:: *)
(*Metric*)


computeProp[g_Graph, "Metric"] := Module[{bps, bps2, reps, verts},
	If[EdgeList[g]==={}, Return[{{1}}&]];
	
	(*shift heads of vertices in ordered paths to the left, remove the leaves (that now are wrapped in iRoot)*)
	bps = findOrderedBinaryTreePaths[g];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	
	(*make replacement rules to renumber vertex arguments from 2 to n*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All,All,1]]}, Thread[list -> 1+ Range@ Length@ list]];
	(*get original set of vertices (without the leaves)*)
	verts = DeleteDuplicates@ Flatten@ bps[[All,;;-2]];
	
	(*follow the path to each non-leaf vertex to define the metric via the Lam\[EAcute] factors; the heads are shifted left like was done above*)
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts],#][[1]]& /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	Hold[Evaluate[DiagonalMatrix[Join[{1,"R"}, "R"*(Times@@@ Rest[bps2] /. reps)]^2]]] /. 
		{iL[n_Integer] :> Sin[#[[n]]], 
		iR[n_Integer] :> Cos[#[[n]]], 
		"R" :> #[[1]], 
		Hold->Function}
]


(* ::Subsubsection::Closed:: *)
(*MetricTensor*)


computeProp[g_Graph, "MetricTensor"] := Module[{bps, bps2, reps, verts, L},
	If[EdgeList[g]==={}, Return[{{1}}&]];
	
	(*shift heads of vertices in ordered paths to the left, remove the leaves (that now are wrapped in iRoot)*)
	bps = findOrderedBinaryTreePaths[g];
	L = Length[bps];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	
	(*make replacement rules to renumber vertex arguments from 2 to n*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All,All,1]]}, Thread[list -> 1+ Range@ Length@ list]];
	(*get original set of vertices (without the leaves)*)
	verts = DeleteDuplicates@ Flatten@ bps[[All,;;-2]];
	
	(*follow the path to each non-leaf vertex to define the metric via the Lam\[EAcute] factors; the heads are shifted left like was done above*)
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts],#][[1]]& /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	Hold[Evaluate[
		SymbolicTensors`Tensor[
			DiagonalMatrix[Join[{1,"R"}, "R"*(Times@@@ Rest[bps2] /. reps)]^2],
			{
				SymbolicTensors`CotangentBasis["head" /@ Range[L]],
				SymbolicTensors`CotangentBasis["head" /@ Range[L]]
			}
		]
	]] /. { iL[n_Integer] :> Sin[#[[n]]], iR[n_Integer] :> Cos[#[[n]]], 
		"R" :> #[[1]], "head"[n_Integer] :> #[[n]], Hold->Function}
]


(* ::Subsubsection::Closed:: *)
(*OrthonormalBasis*)


computeProp[g_Graph, "OrthonormalBasis"] := Module[{bps, bps2, reps, verts, L},
	If[EdgeList[g]==={}, Return[{{1}}&]];
	
	(*shift heads of vertices in ordered paths to the left, remove the leaves (that now are wrapped in iRoot)*)
	bps = findOrderedBinaryTreePaths[g];
	L = Length[bps];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	
	(*make replacement rules to renumber vertex arguments from 2 to n*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All,All,1]]}, Thread[list -> 1+ Range@ Length@ list]];
	(*get original set of vertices (without the leaves)*)
	verts = DeleteDuplicates@ Flatten@ bps[[All,;;-2]];
	
	(*follow the path to each non-leaf vertex to define the metric via the Lam\[EAcute] factors; the heads are shifted left like was done above*)
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts],#][[1]]& /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2]&,#]&, Transpose[{RotateLeft /@ bps[[All,All,0]], bps[[All,All,1]]}]][[All,;;-2]];
	Hold[
	Evaluate@SymbolicTensors`TransformedBasis[
		SymbolicTensors`TangentBasis["head" /@ Range[L]],
		DiagonalMatrix[Join[{1,"R"}, "R"*(Times@@@ Rest[bps2] /. reps)]^-1] 
		]
	] /. {iL[n_Integer] :> Sin[#[[n]]], iR[n_Integer] :> Cos[#[[n]]], 
		"R" :> #[[1]], "head"[n_Integer] :> #[[n]], Hold->Function}
]


(* ::Subsubsection::Closed:: *)
(*ParameterRangeAssumptions*)


computeProp[g_Graph, "ParameterRangeAssumptions"] := True


(* ::Subsubsection::Closed:: *)
(*Properties*)


computeProp[g_Graph, "Properties"] := {"AlternateCoordinateNames","CoordinateRangeAssumptions","Dimension","InverseMetric","Metric","ParameterRangeAssumptions","ScaleFactors","StandardCoordinateNames","StandardName","VolumeFactor"}


(* ::Subsubsection::Closed:: *)
(*ScaleFactors*)


computeProp[g_Graph, "ScaleFactors"] := Module[{bps, bps2, reps, verts},
	If[EdgeList[g]==={}, Return[{1}&]];

	(*find branch paths, shift heads to the left and remove leaf vertex from each path*)
	bps = findOrderedBinaryTreePaths[g];
	bps2 = Map[MapThread[#1[#2] &, #] &, Transpose[{RotateLeft /@ bps[[All, All, 0]], bps[[All, All, 1]]}]][[All, ;; -2]];
	
	(*create replacement rules to number iL, iR, and iRoot arguments from 1 to nLeaves*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All, All, 1]]}, Thread[list -> 1+ Range@ Length@ list]];

	(*remove leaf vertices from each path, find paths from iRoot to each vertices, shift heads to the left and remove last vertex from each path*)
	verts = DeleteDuplicates@ Flatten@ bps[[All, ;; -2]];
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts], #][[1]] & /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2] &, #] &, Transpose[{RotateLeft /@ bps[[All, All, 0]], bps[[All, All, 1]]}]][[All, ;; -2]];

	(*convert paths to scale factors as a pure function*)
	Hold[Evaluate[Join[{1, "R"}, "R" (Times @@@ Rest[bps2] /. reps)]]] /. {
		"R" :> #[[1]], 
		iL[n_Integer] :> Sin[#[[n]]], 
		iR[n_Integer] :> Cos[#[[n]]], 
		Hold -> Function}	
]


(* ::Subsubsection::Closed:: *)
(*StandardCoordinateNames*)


computeProp[g_Graph, "StandardCoordinateNames"] := Module[{gb, bps, res, i,j,k,l},
	If[EdgeList[g]==={}, Return[{}]];

	gb = Sort /@ GatherBy[EdgeList[g], First];
	gb = gb /. {DirectedEdge[x1_,y1_], DirectedEdge[x1_,y2_]} :> {x1, {VertexOutDegree[g,y1], VertexOutDegree[g,y2]}};
	gb = Rule@@@ (gb /. {{2,0} -> "\[Theta]", {0,2} -> OverBar["\[Theta]"], {2,2} -> "\[Alpha]", {0,0} -> "\[CurlyPhi]"});
	bps = findOrderedBinaryTreePaths[g];
	res = DeleteDuplicates@ Flatten@ bps[[All,;;-2]] /. gb;
	{i,j,k,l}={0,0,0,0};
	Join[{"R"}, res] /. {
		"\[Alpha]" :> (i++; Subscript["\[Alpha]", i]),
		"\[Theta]" :> (j++; Subscript["\[Theta]", j]),
		OverBar["\[Theta]"] :> (k++; Subscript[OverBar["\[Theta]"], k]),
		"\[CurlyPhi]" :> (l++; Subscript["\[CurlyPhi]", l])
	}
]


(* ::Subsubsection::Closed:: *)
(*StandardName*)


computeProp[g_Graph, "StandardName"] := {"Hyperspherical", "Euclidean", g}


(* ::Subsubsection::Closed:: *)
(*VolumeFactor*)


computeProp[g_Graph, "VolumeFactor"] := Module[{bps, bps2, reps, verts},
	If[EdgeList[g]==={}, Return[x]];
	
	(*find branch paths, shift heads to the left and remove leaf vertex from each path*)
	bps = findOrderedBinaryTreePaths[g];
	bps2 = Map[MapThread[#1[#2] &, #] &, Transpose[{RotateLeft /@ bps[[All, All, 0]], bps[[All, All, 1]]}]][[All, ;; -2]];
	
	(*create replacement rules to number iL, iR, and iRoot arguments from 1 to nLeaves*)
	reps = With[{list = DeleteDuplicates@ Flatten@ bps2[[All, All, 1]]}, Thread[list -> 1+ Range@ Length@ list]];

	(*remove leaf vertices from each path, find paths from iRoot to each vertices, shift heads to the left and remove last vertex from each path*)
	verts = DeleteDuplicates@ Flatten@ bps[[All, ;; -2]];
	bps = Join[{{iRoot[1]}}, FindPath[g, First[verts], #][[1]] & /@ Rest[verts] ];
	bps2 = Map[MapThread[#1[#2] &, #] &, Transpose[{RotateLeft /@ bps[[All, All, 0]], bps[[All, All, 1]]}]][[All, ;; -2]];

	(*convert paths to scale factors as a pure function*)
	Hold[Evaluate[Times@@ Join[{1, "R"}, ("R"*(Times @@@ Rest[bps2] /. reps))]]] /. {
		"R" :> #[[1]], 
		iL[n_Integer] :> Sin[#[[n]]], 
		iR[n_Integer] :> Cos[#[[n]]], 
		Hold -> Function}	
]


(* ::Subsection::Closed:: *)
(*repair downvalues*)


DownValues[CoordinateChartData] = Join[DownValues[CoordinateChartData], {odvCoordinateChartData}];
Attributes[CoordinateChartData] = {Protected,ReadProtected};


(* ::Section::Closed:: *)
(*SymbolicTensors`SymbolicTensorsDump` changes*)


(*need to add/modify some definitions to allow hyperspherical tree graph as valid entry*)
Begin["SymbolicTensors`SymbolicTensorsDump`"];
possibleCoordinateChartDataSpecQ[{a_,b_,c_Graph?HypersphericalTreeGraphQ}] := possibleCoordinateChartDataSpecQ[{a,b}]
canonicalizePartialCoordinateChartDataSpec[spec_,vars_List] := Module[{fullSpec, dim},
	dim = Length[vars];
	fullSpec = Quiet[Quiet[CoordinateChartData[spec, "FullName", vars]]];
	Replace[fullSpec, Except[{{_String,_},{_String,_},dim|_?HypersphericalTreeGraphQ}] :> $Failed]
]
End[];


(* ::Section::Closed:: *)
(*Grad, Div, Curl, Laplacian*)


(*
These all work now because of 
1. the slight changes made to SymbolicTensors`SymbolicTensorsDump`
2. having the 'DeveloperProperties' defined with CoordinateChartData 
*)


(* ::Section:: *)
(*HypersphericalHarmonicY*)


(* ::Subsection::Closed:: *)
(*angular momentum rule checks*)


(*both subspaces of dim 1 [single dimensions have no angular momenta]*)
parityCheck[{1,1},{0,0},L_] := True

(*one subspace of dim 1, one subspace of dim 2*)
parityCheck[{1,2},{0,l2_},L_] := {L,l2}\[Element]Integers && L>=0 && L>=Abs[l2]>=0
parityCheck[{2,1},{l1_,0},L_] := {L,l1}\[Element]Integers && L>=0 && L>=Abs[l1]>=0

(*both subspaces of dim 2*)
parityCheck[{2,2},{l1_,l2_},L_] := (-1)^L==(-1)^Abs[l1] (-1)^Abs[l2] && {L,l1,l2}\[Element]Integers && L>=0 && L>=Abs[l1]+Abs[l2]>=0

(*one subspace of dim 1, one subspace of dim > 2*)
parityCheck[{1,d2_Integer},{0,l2_},L_] := {L,l2}\[Element]Integers && L>=0 && l2>=0 && L>=l2>=0
parityCheck[{d1_Integer,1},{l1_,0},L_] := {L,l1}\[Element]Integers && L>=0 && l1>=0 && L>=l1>=0

(*one subspace of dim 2, one subspace of dim > 2*)
parityCheck[{2,d2_Integer},{l1_,l2_},L_] := (-1)^L==(-1)^Abs[l1] (-1)^l2 && {L,l1,l2}\[Element]Integers && L>=0 && l2>=0 && L>=Abs[l1]+l2>=0
parityCheck[{d1_Integer,2},{l1_,l2_},L_] := (-1)^L==(-1)^l1 (-1)^Abs[l2] && {L,l1,l2}\[Element]Integers && L>=0 && l1>=0 && L>=l1+Abs[l2]>=0

(*both subspaces of dim > 2*)
parityCheck[{d1_Integer,d2_Integer},{l1_,l2_},L_] := (-1)^L==(-1)^l1 (-1)^l2 && {L,l1,l2}\[Element]Integers && L>=0 && l1>=0 && l2>=0 && L>=l1+l2>=0


(* ::Subsection:: *)
(*angular functions*)


(*two free branches*)
angFunction[{1,1},{0,0},\[Lambda]_,var_] := Exp[I \[Lambda] var]/Sqrt[2 \[Pi]]

(*one free branch*)
oneFreeBranch[2,\[Lambda]_,\[Lambda]1_,\[Beta]_] := With[{\[Mu]=Abs[\[Lambda]1]}, ((Gamma[\[Lambda]+\[Mu]+1] (2 \[Lambda]+1) (\[Lambda]-\[Mu])!)/(2^(2 \[Mu]+1) Gamma[\[Lambda]+1] Gamma[\[Lambda]+1]))^(1/2) Sin[\[Beta]]^\[Mu] JacobiP[\[Lambda]-\[Mu],\[Mu],\[Mu],Cos[\[Beta]]]]
oneFreeBranch[d1_,\[Lambda]_,\[Lambda]1_,\[Beta]_] := ((Gamma[\[Lambda]+\[Lambda]1+d1-1] (2 \[Lambda]+d1-1) (\[Lambda]-\[Lambda]1)!)/(2^(2 \[Lambda]1+d1-1) Gamma[\[Lambda]+d1/2] Gamma[\[Lambda]+d1/2]))^(1/2) Sin[\[Beta]]^\[Lambda]1 JacobiP[\[Lambda]-\[Lambda]1,\[Lambda]1+(d1-2)/2,\[Lambda]1+(d1-2)/2,Cos[\[Beta]]]
angFunction[{1,d2_},{0,\[Lambda]2_},\[Lambda]_,var_] := oneFreeBranch[d2,\[Lambda],\[Lambda]2,\[Pi]/2-var]
angFunction[{d1_,1},{\[Lambda]1_,0},\[Lambda]_,var_] := oneFreeBranch[d1,\[Lambda],\[Lambda]1,var]

(*no free branches*)
noFreeBranches[2,2,\[Lambda]_,\[Lambda]1_,\[Lambda]2_,\[Alpha]_] := With[{m1=Abs[\[Lambda]1],m2=Abs[\[Lambda]2]}, (((2 \[Lambda]+2) Gamma[(m1+m2+\[Lambda]+2)/2] ((\[Lambda]-m1-m2)/2)!)/(Gamma[(\[Lambda]+m1-m2+2)/2] Gamma[(\[Lambda]+m2-m1+2)/2]))^(1/2) Sin[\[Alpha]]^m1 Cos[\[Alpha]]^m2 JacobiP[(\[Lambda]-m1-m2)/2,m1,m2,Cos[2 \[Alpha]]]]
noFreeBranches[2,d2_,\[Lambda]_,\[Lambda]1_,\[Lambda]2_,\[Alpha]_] := With[{m1=Abs[\[Lambda]1]}, (((2 \[Lambda]+d2) Gamma[(m1+\[Lambda]2+\[Lambda]+d2)/2] ((\[Lambda]-m1-\[Lambda]2)/2)!)/(Gamma[(\[Lambda]+m1-\[Lambda]2+2)/2] Gamma[(\[Lambda]+\[Lambda]2-m1+d2)/2]))^(1/2) Sin[\[Alpha]]^m1 Cos[\[Alpha]]^\[Lambda]2 JacobiP[(\[Lambda]-m1-\[Lambda]2)/2,m1,\[Lambda]2+d2/2-1,Cos[2 \[Alpha]]]]
noFreeBranches[d1_,2,\[Lambda]_,\[Lambda]1_,\[Lambda]2_,\[Alpha]_] := With[{m2=Abs[\[Lambda]2]}, (((2 \[Lambda]+d1) Gamma[(\[Lambda]1+m2+\[Lambda]+d1)/2] ((\[Lambda]-\[Lambda]1-m2)/2)!)/(Gamma[(\[Lambda]+\[Lambda]1-m2+d1)/2] Gamma[(\[Lambda]+m2-\[Lambda]1+2)/2]))^(1/2) Sin[\[Alpha]]^\[Lambda]1 Cos[\[Alpha]]^m2 JacobiP[(\[Lambda]-\[Lambda]1-m2)/2,\[Lambda]1+d1/2-1,m2,Cos[2 \[Alpha]]]]
noFreeBranches[d1_,d2_,\[Lambda]_,\[Lambda]1_,\[Lambda]2_,\[Alpha]_] := (((2 \[Lambda]+d1+d2-2) Gamma[(\[Lambda]1+\[Lambda]2+\[Lambda]+d1+d2-2)/2] ((\[Lambda]-\[Lambda]1-\[Lambda]2)/2)!)/(Gamma[(\[Lambda]+\[Lambda]1-\[Lambda]2+d1)/2] Gamma[(\[Lambda]+\[Lambda]2-\[Lambda]1+d2)/2]))^(1/2) Sin[\[Alpha]]^\[Lambda]1 Cos[\[Alpha]]^\[Lambda]2 JacobiP[(\[Lambda]-\[Lambda]1-\[Lambda]2)/2,\[Lambda]1+d1/2-1,\[Lambda]2+d2/2-1,Cos[2 \[Alpha]]]
angFunction[{d1_,d2_},{\[Lambda]1_,\[Lambda]2_},\[Lambda]_,var_] := noFreeBranches[d1,d2,\[Lambda],\[Lambda]1,\[Lambda]2,var]


(* ::Subsection:: *)
(*main*)


HypersphericalHarmonicY::quantaNoInt="The numeric entries of quanta `1` must all be integers.";
HypersphericalHarmonicY::badLengths="The number of quantum numbers `1` must equal the number of variables `2`, and be one less than the number of hyperspherical tree leaves `3`.";
HypersphericalHarmonicY::notFlat="The list of quanta and variables contain sublists."


HypersphericalHarmonicY[quanta_List, var_List, g_?HypersphericalTreeGraphQ] := Module[
{roots, branchPairs, dim, lambdas, leaves, l1, l2, l3, restriction},
	l1 = Length[quanta];
	l2 = Length[var];
	leaves = findBinaryTreeLeaves[g];
	l3 = Length[leaves];
	
	(*check that quanta and var have same length, and agree with one less than the number of tree leaves*)
	If[Not[l1 == l2 == l3-1], 
		Message[HypersphericalHarmonicY::badLengths, l1, l2, l3];
		Return[Defer[HypersphericalHarmonicY[quanta, var, g]]]
	];
	
	(*check that numeric entries of quanta list are integers*)
	If[!AllTrue[Cases[quanta, NumericQ], IntegerQ], 
		Message[HypersphericalHarmonicY::canonical, quanta];
		Return[Defer[HypersphericalHarmonicY[quanta, var, g]]]
	];
	
	(*check that non-numeric entries of quanta and var are not lists*)
	If[Count[quanta, _List] + Count[var, _List] > 0,
		Message[HypersphericalHarmonicY::notFlat];
		Return[Defer[HypersphericalHarmonicY[quanta, var, g]]]
	];
	
	roots = SortBy[Cases[VertexList[g], _[x_] /; x < l3], First];
	branchPairs = Map[Sort, EdgeList[g, # \[DirectedEdge] _][[All,-1]]& /@ roots];
	dim = Map[Length[Intersection[VertexOutComponent[g,{#}],leaves]]&, branchPairs, {2}];
	lambdas = branchPairs /. Join[Thread[roots -> quanta], {(iL|iR)[_] -> 0}];
	
	(*check that list of quanta does not violate parity rules*)
	restriction = FullSimplify[And @@ MapThread[parityCheck, {dim, lambdas, quanta}]];
	If[restriction === False, 
		Return[0],
		Return[ConditionalExpression[Times @@ MapThread[angFunction, {dim, lambdas, quanta, var}], restriction]]
	];	
]


(* ::Section:: *)
(*End*)


End[]

EndPackage[]
