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

func (dNode DiscriminationNode) getChildren() Lib.List[DiscriminationNode] {
	return dNode.children
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

//[-----PARSER-----]

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

//[---FIN PARSER---]

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

func (dNode DiscriminationNode) GetASTAtDepth(depth int) []SymbolType {

	res := []SymbolType{}
	if depth == 0 {
		if !dNode.IsEmpty() {
			res = append(res, dNode.symbol)
		}
		return res
	}

	for _, child := range dNode.children.GetSlice() {
		res = append(res, child.GetASTAtDepth(depth-1)...)
	}

	return res

}

// Equals between tow SymbolType
func (s SymbolType) Equals(target SymbolType) bool {

	if ok := s.getSymbol().Equals(target.getSymbol()); ok {
		if s.GetArity() != target.GetArity() {
			Glob.Anomaly("Pred Error", "Same predicat but different arity")
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

func (dNode DiscriminationNode) SkipTreeTermAndContinue(needed int, remainingQuery []SymbolType) Lib.List[AST.Pred] {

	res := Lib.NewList[AST.Pred]()

	// End of recursion
	if needed == 0 {
		return dNode.retrieveRec(remainingQuery)
	}

	for _, child := range dNode.children.GetSlice() {
		newNeeded := needed - 1 + child.GetArity() // 0 if Meta, Else Arity of the Term
		matches := child.SkipTreeTermAndContinue(newNeeded, remainingQuery)
		res.Append(matches.GetSlice()...)
	}

	return res

}

func (dNode DiscriminationNode) RetrieveUnifiables(t AST.Form) Lib.List[AST.Pred] {
	seq := parseFormula(t).GetSlice()
	return dNode.retrieveRec(seq)
}

func (dNode DiscriminationNode) retrieveRec(seq []SymbolType) Lib.List[AST.Pred] {

	res := Lib.NewList[AST.Pred]()
	if len(seq) == 0 { // End of recursion
		res.Append(dNode.leafFor.GetSlice()...) // Append leafFor of this node
		return res
	}

	symQuery := seq[0] // First Element

	for _, child := range dNode.children.GetSlice() {

		isExactMatch := child.symbol.Equals(symQuery)

		// Exact Match
		if isExactMatch {

			matches := child.retrieveRec(seq[1:]) // Exact Match -> Search next element
			res.Append(matches.GetSlice()...)
		}

		symChild := child.getSymbol()

		// Case the child is a AST.Meta
		if symChild != nil && symChild.IsMeta() && !isExactMatch {

			// We noticed that the term of the dNode is a Meta
			// Meaning that we can skip the current term of the seq ( paramater of this function ) bc it will be unify with the current term
			// e.g dNode = x, seq = [f,a] so [f,a] |-> x and we skip 2 because GetSbTermLength of [f,a] is 2
			skip := GetSubTermLength(seq)
			if skip <= len(seq) { // Security to prevent segfault
				matches := child.retrieveRec(seq[skip:])
				res.Append(matches.GetSlice()...)
			}

			// First element is a meta
		} else if symQuery.getSymbol() != nil && symQuery.getSymbol().IsMeta() && !isExactMatch {
			// Reverse of the situation with the previous if.
			// The symbol from seq ( parameter of this function ) is a Meta, meaning we skip the current term of dNode because it will be unify
			// e.g dNode = a, seq = [x] so a |-> x and we got to the next term of the dNode
			matches := child.SkipTreeTermAndContinue(child.GetArity(), seq[1:])
			res.Append(matches.GetSlice()...)
		}
	}

	return res
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
				fmt.Println("Cas not apres cast pour Pred", newForm)
				dNode = dNode.Insert(newForm)
			}
		}
	}
	return dNode
}

// TODO
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

	// For Robinson
	queryTerm := subst.TransformPred(predFormula)

	for _, possibleMatch := range candidates.GetSlice() {

		possibleMatchTerm := subst.TransformPred(possibleMatch) // Pred -> Term for Robinson
		emptySubst := subst.Substitutions{}
		finalSubst := subst.AddUnification(possibleMatchTerm, queryTerm, emptySubst) // Call Robinson

		if finalSubst.Equals(subst.Failure()) {
			fmt.Println("-------------------------")
			fmt.Println("Echec Substitution")
			fmt.Println("-------------------------")
		}

		if !finalSubst.Equals(subst.Failure()) {
			found = true
			matching := subst.MakeMatchingSubstitutions(possibleMatch, finalSubst) // constructor
			mixed = append(mixed, matching.ToMixed())                              // convert To Mixed for return
		}
	}
	return found, mixed
}

// TODO
func (dNode DiscriminationNode) UnifyTerm(t AST.Term) (bool, []subst.MixedTermSubstitutions) {

	var mixed []subst.MixedTermSubstitutions
	var found bool

	seq := parseTerm(t).GetSlice()
	candidates := dNode.retrieveRec(seq)

	for _, possibleMatch := range candidates.GetSlice() {

		candidateTerm := subst.TransformPred(possibleMatch)
		emptySubst := subst.Substitutions{}
		finalSubst := subst.AddUnification(candidateTerm, t, emptySubst) // Call Robinson

		if !finalSubst.Equals(subst.Failure()) {
			found = true

			mixMatch := subst.MixMatchSubstitutions{
				Tof:   Lib.MkLeft[AST.Term, AST.Form](candidateTerm),
				Subst: finalSubst,
			}
			mixed = append(mixed, mixMatch.ToMixedTerm())
		}

	}

	return found, mixed

}

func (dNode DiscriminationNode) MakeDataStruct(Formulas Lib.List[AST.Form], is_pos bool) subst.DataStructure {
	// Gerer cas possitif ou negatif
	return dNode.InsertFormulaListToDataStructure(Formulas)
}
