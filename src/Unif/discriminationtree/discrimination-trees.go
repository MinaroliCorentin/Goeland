/**
* Copyright 2022 by the authors (see AUTHORS).
*
* Goéland is an automated theorem prover for first order logic.
*
* This software is governed by the CeCILL license under French law and
* abiding by the rules of distribution of free software.  You can  use,
* modify and/ or redistribute the software under the terms of the CeCILL
* license as circulated by CEA, CNRS and INRIA at the following URL
* "http://www.cecill.info".
*
* As a counterpart to the access to the source code and  rights to copy,
* modify and redistribute granted by the license, users are provided only
* with a limited warranty  and the software's author,  the holder of the
* economic rights,  and the successive licensors  have only  limited
* liability.
*
* In this respect, the user's attention is drawn to the risks associated
* with loading,  using,  modifying and/or developing or reproducing the
* software by the user in light of its specific status of free software,
* that may mean  that it is complicated to manipulate,  and  that  also
* therefore means  that it is reserved for developers  and  experienced
* professionals having in-depth computer knowledge. Users are therefore
* encouraged to load and test the software's suitability as regards their
* requirements in conditions enabling the security of their systems and/or
* data to be ensured and,  more generally, to use and operate it in the
* same conditions as regards security.
*
* The fact that you are presently reading this means that you have had
* knowledge of the CeCILL license and that you accept its terms.
**/

/**
* This file contains all the definitons necessary to make a Code Tree
**/

package discriminationtree

import (
	"fmt"
	"strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	subst "github.com/GoelandProver/Goeland/Unif/substitution"
)

/*************************/
/* Structures definition */
/*************************/

type SymbolType struct {
	symbol AST.Term // Term of the node
	arity  int      // Arity of a node
}

func (t SymbolType) getSymbol() AST.Term {
	return t.symbol
}

func (t SymbolType) GetArity() int {
	return t.arity
}

func (s SymbolType) IsNil() bool {
	return s.symbol == nil && s.arity == -1
}

func makeSymbolType(t AST.Term, arity int) SymbolType {
	return SymbolType{t, arity}
}

/* Each node of a CodeTree is composed of a sequence of instruction and its children. If it's a leaf, it has formulaes corresponding to the sequence of instructions. */
type DiscriminationNode struct {
	symbol   SymbolType                   // Contain the AST.Term and Arity
	children Lib.List[DiscriminationNode] // All the children of the node
	leafFor  Lib.List[AST.Pred]           // If not empty, contains the where it come from
}

// Basic Node with no data inside
func NewNode() DiscriminationNode {
	return DiscriminationNode{
		symbol:   SymbolType{symbol: nil, arity: -1},
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

func MakeNodeWithSym(sym SymbolType) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

func (dNode *DiscriminationNode) setSymbol(symbol SymbolType) {
	dNode.symbol = symbol
}

func (dNode DiscriminationNode) GetArity() int {
	return dNode.symbol.GetArity()
}

func (dNode DiscriminationNode) getSymbol() AST.Term {
	return dNode.symbol.getSymbol()
}

func (dNode DiscriminationNode) IsEmpty() bool {
	return dNode.symbol.IsNil()
}

func (dNode DiscriminationNode) ToString() string {
	return dNode.getSymbol().ToString()
}

type CandidatResult struct {
	Pred AST.Pred
	Subs subst.Substitutions
}

func (Candidat CandidatResult) getPred() AST.Pred {
	return Candidat.Pred
}

func (Candidat CandidatResult) GetSubs() subst.Substitutions {
	return Candidat.Subs
}

func MakeCandidat(p AST.Pred, sub subst.Substitutions) CandidatResult {
	return CandidatResult{
		Pred: p,
		Subs: sub,
	}
}

func MakeCandidatResultWithPred(p AST.Pred) CandidatResult {
	return CandidatResult{
		Pred: p,
		Subs: subst.Substitutions{},
	}
}

/*****************************/
/* End Structures definition */
/*****************************/

/*****************************/
/*********** Parse ***********/
/*****************************/

func parseFormula(formula AST.Form) Lib.List[SymbolType] {
	res := Lib.NewList[SymbolType]()
	// The formula has to be a predicate
	switch formula_type := formula.(type) {
	case AST.Pred:
		first_element := makeSymbolType(formula_type.GetID(), formula_type.GetArgs().Len())
		res.Append(first_element)
		for _, arg := range formula_type.GetArgs().GetSlice() {
			arg_list := parseTerm(arg)
			res.Append(arg_list.GetSlice()...)
		}
		return res
	default:
		return Lib.NewList[SymbolType]()
	}
}

// Parser for a formula : f(x,y) -> [f,x,y], a -> [a], x -> [x]
func parseTerm(t AST.Term) Lib.List[SymbolType] {
	res := Lib.NewList[SymbolType]()
	// The formula has to be a predicate

	switch term := t.(type) {
	case AST.Fun: // Add all the args of the function
		first_element := makeSymbolType(term.GetID(), term.GetArgs().Len()) // Add the node before recursive call
		res.Append(first_element)
		for _, arg := range term.GetArgs().GetSlice() {
			res.Append(parseTerm(arg).GetSlice()...)
		}
	case AST.Meta:
		res.Append(makeSymbolType(term, 0))
	}

	return res
}

/*****************************/
/********* End Parse *********/
/*****************************/

/*****************************/
/********* Transform *********/
/*****************************/

func FirstElementToSymbolType(t AST.Term) SymbolType {
	switch t := t.(type) {
	case AST.Fun: // Case function
		return SymbolType{t.GetID(), t.GetArgs().Len()}
	case AST.Meta: // Case metaVariable
		return SymbolType{t, 0}
	default: // Not supposed to see something else
		Glob.Anomaly("TermToST", "Var or Id")
		return SymbolType{nil, -1}
	}
}

func TermToNode(t AST.Term) DiscriminationNode {
	switch t := t.(type) {
	case AST.Fun:
		children := Lib.NewList[DiscriminationNode]()
		for _, c := range t.GetArgs().GetSlice() {
			children.Append(TermToNode(c))
		}

		// Node with all his children
		return DiscriminationNode{FirstElementToSymbolType(t), children, Lib.NewList[AST.Pred]()}
	case AST.Meta:
		return DiscriminationNode{FirstElementToSymbolType(t), Lib.NewList[DiscriminationNode](), Lib.NewList[AST.Pred]()}
	default:
		Glob.Anomaly("TermToST", "Var or Id")
		return NewNode()
	}
}

/*****************************/
/******* End Transform *******/
/*****************************/

func (dNode DiscriminationNode) Print() {
	for _, child := range dNode.children.GetSlice() {
		child.displayRec(2) // Magic Number
	}
}

func (dNode DiscriminationNode) displayRec(indent int) {

	prefix := strings.Repeat("    ", indent-1) + " |-- "

	if indent == 2 {
		prefix = strings.Repeat("[ROOT]", indent-1) + " |-- "
	}

	fmt.Printf("%s%s arity : %d\n", prefix, dNode.getSymbol().ToString(), dNode.GetArity())

	if dNode.leafFor.Len() > 0 {
		leafPrefix := strings.Repeat("    ", indent) + " [=> "
		for _, pred := range dNode.leafFor.GetSlice() {
			fmt.Printf("%s%s]\n", leafPrefix, pred.ToString())
		}
	}

	for _, child := range dNode.children.GetSlice() {
		child.displayRec(indent + 1)
	}
}

// Equals between two SymbolType
func (s SymbolType) Equals(target SymbolType) bool {

	if ok := s.getSymbol().Equals(target.getSymbol()); ok {
		if s.GetArity() != target.GetArity() {
			fmt.Printf("Symbol Arity : %d, Target Arity : %d", s.GetArity(), target.GetArity())
			Glob.Anomaly("Pred Error", "Same predicat but different arity ")
		} else {
			return true
		}
	}
	return false
}

func (dNode DiscriminationNode) Insert(p AST.Pred) DiscriminationNode {
	sym_list := parseFormula(p)
	return dNode.insertRec(sym_list, p)
}

func (dNode DiscriminationNode) insertRec(seq Lib.List[SymbolType], originalTerm AST.Pred) DiscriminationNode {

	// End of recursion, time to insert
	if seq.Len() == 0 {
		Exist := false
		for _, pred := range dNode.leafFor.GetSlice() {
			if pred.Equals(originalTerm) {
				Exist = true
				break
			}
		}
		if !Exist {
			dNode.leafFor.Append(originalTerm)
		}
		return dNode
	}

	// Create Symbol
	sym := seq.At(0)
	foundIndex := -1
	childrenSlice := dNode.children.GetSlice()

	// Looking for already existing child
	var ok bool
	for i, child := range childrenSlice {
		if ok = child.symbol.Equals(sym); ok { // Set ok to True
			foundIndex = i
			break
		}
	}

	// Child already exist
	if ok {

		// Insert and update the sequence
		updatedChild := childrenSlice[foundIndex].insertRec(seq.RemoveAt(0), originalTerm)
		dNode.children.Upd(foundIndex, updatedChild) // Update children[foundIntex] = updateChild
		// if Child doesn't exist
	} else {

		newChild := MakeNodeWithSym(sym)                                  // Create a new Node with the new SymbolType
		updatedChild := newChild.insertRec(seq.RemoveAt(0), originalTerm) // Insert the rest of the sequence after the new child
		dNode.children.Append(updatedChild)                               // Update the children of the args node
	}
	return dNode // Return updated node
}

func GetSubTermLength(seq []SymbolType) int {

	if len(seq) == 0 {
		return 0
	}

	needed := 1
	index := 0

	for needed > 0 && index < len(seq) {
		sym := seq[index]
		needed = needed - 1 + sym.arity // If Arity == 0 ( Meta ) end this loop, else add the arity of the form/func/...
		index++
	}
	return index

}

func (dNode DiscriminationNode) SkipTreeTermAndContinue(needed int, remainingQuery []SymbolType, substitutions subst.Substitutions) []CandidatResult {

	var subs []CandidatResult

	// End of recursion
	if needed == 0 {
		return dNode.retrieveRec(remainingQuery, substitutions)
	}

	for _, child := range dNode.children.GetSlice() {
		newNeeded := needed - 1 + child.GetArity() // 0 if Meta, Else Arity of the Term
		matches := child.SkipTreeTermAndContinue(newNeeded, remainingQuery, substitutions)
		subs = append(subs, matches...)
	}

	return subs

}

func (dNode DiscriminationNode) RetrieveUnifiables(t AST.Form) []CandidatResult {
	seq := parseFormula(t).GetSlice()
	Env := subst.Substitutions{}
	return dNode.retrieveRec(seq, Env)
}

func (dNode DiscriminationNode) retrieveRec(seq []SymbolType, currentEnv subst.Substitutions) []CandidatResult {

	var results []CandidatResult

	// Voir pour la suite, est-ce necessaire de faire ceci alors que Robinson a déjà vérifier les blocs précédent, notamment celui juste avant de ce rendre compte que cette partie va fonctionner ou non
	if len(seq) == 0 { // End of recursion
		for _, p := range dNode.leafFor.GetSlice() {
			results = append(results, MakeCandidat(p, currentEnv))
		}
		return results
	}

	symQuery := seq[0] // First Element

	// fmt.Println("RetrieveRec SymQuery", symQuery.getSymbol().ToString())

	for _, child := range dNode.children.GetSlice() {

		isExactMatch := child.symbol.Equals(symQuery)
		// fmt.Println("Exact Match", child.getSymbol())
		if isExactMatch { // Exact Match
			matches := child.retrieveRec(seq[1:], currentEnv) // Exact Match -> Search next element
			results = append(results, matches...)
		}

		symChild := child.getSymbol()

		// Case the child is a AST.Meta
		if symChild != nil && symChild.IsMeta() && !isExactMatch {

			// We noticed that the term of the dNode is a Meta
			// Meaning that we can skip the current term of the seq ( paramater of this function ) bc it will be unify with the current term
			// e.g dNode = x, seq = [f,a] so [f,a] |-> x and we skip 2 because GetSbTermLength of [f,a] is 2
			skip := GetSubTermLength(seq)

			// fmt.Println("Longueur du skip", skip)

			if skip <= len(seq) { // Security to prevent segfault

				var mergedSub subst.Substitutions
				if skip == 1 {
					currentSub := subst.MakeSubstitution(symChild.ToMeta(), symQuery.getSymbol())
					tmp3 := subst.Substitutions{currentSub}
					// Ok Commat Idoms doesn't works because ??????????????????????????????
					if len(currentEnv) == 0 {
						mergedSub = tmp3
					} else {
						mergedSub, _ = subst.MergeSubstitutions(currentEnv, tmp3)
					}

				} else {
					mergedSub = currentEnv
				}

				// Verify
				if !mergedSub.Equals(subst.Failure()) {
					matches := child.retrieveRec(seq[skip:], mergedSub)
					results = append(results, matches...)
				}

			}

			// First element is a meta
		} else if symQuery.getSymbol() != nil && symQuery.getSymbol().IsMeta() && !isExactMatch {
			// Reverse of the situation with the previous if.
			// The symbol from seq ( parameter of this function ) is a Meta, meaning we skip the current term of dNode because it will be unify
			// e.g dNode = a, seq = [x] so a |-> x and we got to the next term of the dNode

			var mergedSub subst.Substitutions
			if child.GetArity() == 0 {
				currentSub := subst.MakeSubstitution(symQuery.getSymbol().ToMeta(), symChild) // Create a new substitution
				tmp3 := subst.Substitutions{currentSub}
				if len(currentEnv) == 0 {
					mergedSub = tmp3
				} else {
					mergedSub, _ = subst.MergeSubstitutions(currentEnv, tmp3)
				}
			} else {
				mergedSub = currentEnv
			}

			if !mergedSub.Equals(subst.Failure()) {
				childResults := child.SkipTreeTermAndContinue(child.GetArity(), seq[1:], mergedSub)
				results = append(results, childResults...)

				// for _, elem := range results {
				// fmt.Println("elem pred Query meta", elem.getPred().ToString())
				// fmt.Println("elem pred Query meta", elem.GetSubs().ToString())
				// }
			}

		} else {
			continue
		}
	}
	return results
}

func (dNode DiscriminationNode) Copy() subst.DataStructure {

	newChildMaster := Lib.NewList[DiscriminationNode]()
	for _, child := range dNode.children.GetSlice() {
		newChild := child.Copy().(DiscriminationNode)
		newChildMaster.Append(newChild)
	}

	newLeafFor := Lib.ListCpy(dNode.leafFor)
	return DiscriminationNode{symbol: dNode.symbol, children: newChildMaster, leafFor: newLeafFor}

}

func (dNode DiscriminationNode) InsertFormulaListToDataStructure(lf Lib.List[AST.Form]) subst.DataStructure {
	fmt.Println("Form")
	for _, f := range lf.GetSlice() {
		fmt.Println("element f", f.ToString())
		switch nf := f.Copy().(type) {
		case AST.Pred:
			fmt.Println("Cas Pred")
			dNode = dNode.Insert(nf)
		case AST.Not:
			fmt.Println("Cas not")
			switch newForm := nf.GetForm().(type) { // Get the type AST.Form
			case AST.Pred:
				fmt.Println("Cas not apres cast pour Pred", newForm.ToString())
				dNode = dNode.Insert(newForm)
			}
		}
	}
	return dNode
}

func (dNode DiscriminationNode) Unify(inputFormula AST.Form) (bool, []subst.MixedSubstitutions) {

	candidates := dNode.RetrieveUnifiables(inputFormula)
	var mixed []subst.MixedSubstitutions
	var found bool

	// Robinson required Pred, so we verify
	predFormula, isPred := inputFormula.(AST.Pred)
	if !isPred {
		Glob.Anomaly("DiscriminationTree Unify", "Expected a predicate")
		return false, nil
	}

	queryTerm := subst.TransformPred(predFormula) // For Robinson

	for _, possibleMatch := range candidates {

		initialSubst := subst.Substitutions{}
		possibleMatchTerm := subst.TransformPred(possibleMatch.getPred())              // Pred -> Term for Robinson
		finalSubst := subst.AddUnification(possibleMatchTerm, queryTerm, initialSubst) // Call Robinson

		// fmt.Println("Unify initialSubst", initialSubst.ToString())
		// fmt.Println("Unify possibleMatchTerm", possibleMatchTerm.ToString())
		// fmt.Println("Unify finalSubst", finalSubst.ToString())

		if finalSubst.Equals(subst.Failure()) {
			fmt.Println("-------------------------")
			fmt.Println("Substitution FAILURE")
			fmt.Println("-------------------------")
		} else {
			found = true
			matching := subst.MakeMatchingSubstitutions(inputFormula, finalSubst) // constructor
			mixed = append(mixed, matching.ToMixed())                             // convert To Mixed for return
		}
	}
	return found, mixed
}

func (dNode DiscriminationNode) UnifyTerm(t AST.Term) (bool, []subst.MixedTermSubstitutions) {

	var mixed []subst.MixedTermSubstitutions
	var found bool

	seq := parseTerm(t).GetSlice()

	// for _, elem := range seq {
	// 	fmt.Println("seq", elem.getSymbol().ToString())
	// }

	candidates := dNode.retrieveRec(seq, subst.MakeEmptySubstitution())

	// for _, elem := range candidates {
	// 	fmt.Println("element", elem.getPred().ToString())
	// }

	for _, possibleMatch := range candidates {

		// fmt.Println("Candidat", possibleMatch.Pred.ToString(), possibleMatch.Subs.ToString())

		candidateTerm := subst.TransformPred(possibleMatch.getPred())
		emptySubst := subst.Substitutions{}
		// fmt.Println("=> candidateTerm : ", candidateTerm.ToString())
		// fmt.Println("=> t : ", t.ToString())
		// fmt.Println("=> EmptySubset : ", emptySubst.ToString())

		finalSubst := subst.AddUnification(t, candidateTerm, emptySubst) // Call Robinson

		// fmt.Println("finalSubst", finalSubst.ToString())

		if !finalSubst.Equals(subst.Failure()) {
			found = true
			mixMatch := subst.MixMatchSubstitutions{
				Tof:   Lib.MkLeft[AST.Term, AST.Form](t),
				Subst: finalSubst,
			}
			mixed = append(mixed, mixMatch.ToMixedTerm())
		} else {
			fmt.Println("-------------------------")
			fmt.Println("Substitution FAILURE")
			fmt.Println("-------------------------")
		}
	}
	return found, mixed
}

func (dNode DiscriminationNode) MakeDataStruct(Formulas Lib.List[AST.Form], is_pos bool) subst.DataStructure {
	// Gérer cas positif ou negatif
	return dNode.InsertFormulaListToDataStructure(Formulas)
}
