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
	"sync"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	subst "github.com/GoelandProver/Goeland/Unif/substitution"
)

var debug Glob.Debugger

func InitDebugger() {
	debug = Glob.CreateDebugger("unif")
}

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

/* Each node of a CodeTree is composed of a sequence of instruction and its children. If it's a leaf, it has formulaes corresponding to the sequence of instructions. */
type DiscriminationNode struct {
	symbol   SymbolType                   // Contain the AST.Term and Arity
	children Lib.List[DiscriminationNode] // All the children of the node
	leafFor  Lib.List[AST.Pred]           // If not empty, contains the where it come from
}

// Basic Node. Create a SymbolType{nil, -1} and empty list for children and leafFor
func NewNode() DiscriminationNode {
	return DiscriminationNode{
		symbol:   SymbolType{symbol: nil, arity: -1},
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

// Basic Node with SymbolType and no empty list for children and leafFor
func MakeNodeWithSym(sym SymbolType) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

func MakeNodeWithSymAndleaf(sym SymbolType, leaf Lib.List[AST.Pred]) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  leaf,
	}
}

// Basic Node with SymbolType, children and empty List for leafFor
func MakeNodeWithSymAndChildren(sym SymbolType, children Lib.List[DiscriminationNode]) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: children,
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

func (dNode DiscriminationNode) getChildren() Lib.List[DiscriminationNode] {
	return dNode.children
}

func (dNode DiscriminationNode) getLeafFor() Lib.List[AST.Pred] {
	return dNode.leafFor
}

func (dNode DiscriminationNode) ToString() string {
	return dNode.getSymbol().ToString()
}

// Struct with a Pred and a associated substitution. Used for Robinson
type CandidatResult struct {
	Pred AST.Pred            // Predicat
	Subs subst.Substitutions // The associated substitution

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

/*****************************/
/* End Structures definition */
/*****************************/

/*****************************/
/*********** Parse ***********/
/*****************************/

func parseFormula(formula AST.Form) Lib.List[SymbolType] {
	res := Lib.NewList[SymbolType]()
	ctx := NewContext() // Context gonna store all the transformations ( X == v1, Y == v2, ...)

	switch formula_type := formula.(type) {
	case AST.Pred:
		// Add First element ( Predicat )
		first_element := makeSymbolType(formula_type.GetID(), formula_type.GetArgs().Len())
		res.Append(first_element)

		// Call the parse on each element of the predicat
		for _, arg := range formula_type.GetArgs().GetSlice() {
			arg_list := parseTerm(arg, ctx)
			res.Append(arg_list.GetSlice()...)
		}
		return res
	default:
		return Lib.NewList[SymbolType]()
	}
}

func parseTerm(t AST.Term, ctx *NormalizerContext) Lib.List[SymbolType] {
	res := Lib.NewList[SymbolType]()

	switch term := t.(type) {

	// if term is a function or cst, add and call his args
	case AST.Fun:
		first_element := makeSymbolType(term.GetID(), term.GetArgs().Len())
		res.Append(first_element)
		for _, arg := range term.GetArgs().GetSlice() {
			res.Append(parseTerm(arg, ctx).GetSlice()...)
		}

	// Case meta, we have to transform it
	case AST.Meta:

		originalName := term.GetName()         // Name of the meta
		_, exists := ctx.mapping[originalName] // Contains
		if !exists {                           // If the meta is unknow
			ctx.counter++
			newName := fmt.Sprintf("v%d", ctx.counter) // v + int. e.g  v1,v2,v3,...
			fakeMeta := AST.MakeMeta(ctx.counter, 0, newName, 0, term.GetTy())
			ctx.mapping[originalName] = fakeMeta // Update the mapping : X -> v1 or Y -> v2 .... )
		}

		normalizedMeta := ctx.mapping[originalName]   // Return the transformed name association to the originalName before adding
		res.Append(makeSymbolType(normalizedMeta, 0)) // Add the new Meta to the return slice

	}
	return res

}

/*****************************/
/********* End Parse *********/
/*****************************/

/*****************************/
/********* Transform *********/
/*****************************/

// Case t is a Function => SymbolType{t.ID, t.getArgs}
// Case t is a Meta => SymbolType{t.ID, 0}
// Else Glob.Anomaly
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
	case AST.Fun: // Accumulate all the term of the AST.Term then create a Node with all the children
		children := Lib.NewList[DiscriminationNode]()
		for _, c := range t.GetArgs().GetSlice() {
			children.Append(TermToNode(c))
		}
		return MakeNodeWithSymAndChildren(FirstElementToSymbolType(t), children)
	case AST.Meta: // Node with T as SymbolType and empty children / leafFor
		return MakeNodeWithSym(FirstElementToSymbolType(t))
	default:
		Glob.Anomaly("TermToST", "Var or Id")
		return NewNode()
	}
}

/*****************************/
/******* End Transform *******/
/*****************************/

/*****************************/
/*********** Insrt ***********/
/*****************************/

// Insert a AST.Pred in the tree. If using a AST.term, it have to be cast when inserting ( tree = tree.Insert(px.(AST.pred)) )
// Call the parser then the auxiliary function
func (dNode DiscriminationNode) Insert(p AST.Pred) DiscriminationNode {
	sym_list := parseFormula(p)
	return dNode.insertRec(sym_list, p)
}

// Auxiliary function for insert.
func (dNode DiscriminationNode) insertRec(seq Lib.List[SymbolType], originalTerm AST.Pred) DiscriminationNode {

	// End of recursion, time to insert
	if seq.Len() == 0 {
		Exist := false
		for _, pred := range dNode.getLeafFor().GetSlice() {
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
	childrenSlice := dNode.getChildren().GetSlice()

	// Looking for already existing child
	var ok bool
	for i, child := range childrenSlice {
		if ok = child.symbol.Equals(sym); ok { // Set ok to True
			foundIndex = i
			break
		}
	}

	if ok { // Child already exist

		// Insert and update the sequence
		updatedChild := childrenSlice[foundIndex].insertRec(seq.RemoveAt(0), originalTerm)
		dNode.children.Upd(foundIndex, updatedChild) // Update children[foundIntex] = updateChild

	} else { // if Child doesn't exist

		newChild := MakeNodeWithSym(sym)                                  // Create a new Node with the new SymbolType and his leafFor
		updatedChild := newChild.insertRec(seq.RemoveAt(0), originalTerm) // Insert the rest of the sequence after the new child
		dNode.children.Append(updatedChild)                               // Update the children of the args node
	}
	return dNode
}

/*****************************/
/********* End insrt *********/
/*****************************/

/*****************************/
/********** Retriev **********/
/*****************************/

func GetSubTermLength(seq []SymbolType) int {

	if len(seq) == 0 {
		return 0
	}

	needed := 1
	index := 0

	for needed > 0 && index < len(seq) {
		sym := seq[index]
		needed = needed - 1 + sym.GetArity() // If Arity == 0 ( Meta ) end this loop, else add the arity of the form/func/...
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

	for _, child := range dNode.getChildren().GetSlice() {
		newNeeded := needed - 1 + child.GetArity() // 0 if Meta, Else Arity of the Term
		matches := child.SkipTreeTermAndContinue(newNeeded, remainingQuery, substitutions)
		subs = append(subs, matches...)
	}
	return subs

}

func retrieveCase(seq []SymbolType, currentEnv subst.Substitutions, child DiscriminationNode, ch chan<- []CandidatResult, wg *sync.WaitGroup) {

	defer wg.Done()
	symQuery := seq[0] // First Element

	isExactMatch := child.symbol.Equals(symQuery)
	if isExactMatch { // Exact Match
		matches := child.retrieveRec(seq[1:], currentEnv) // Exact Match -> Search next element
		ch <- matches
	}

	symChild := child.getSymbol() // child is  meta or cst

	// Case the child is a AST.Meta
	if symChild != nil && symChild.IsMeta() && !isExactMatch {

		// We noticed that the term of the dNode is a Meta
		// Meaning that we can skip the current term of the seq ( paramater of this function ) bc it will be unify with the current term
		// e.g dNode = x, seq = [f,a] so [f,a] |-> x and we skip 2 because GetSbTermLength of [f,a] is 2
		skip := GetSubTermLength(seq)

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
				ch <- matches
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
			ch <- childResults
		}

	} else {
		// No recursive call or return
	}

}

func (dNode DiscriminationNode) RetrieveUnifiables(t AST.Form) []CandidatResult {
	seq := parseFormula(t).GetSlice()
	Env := subst.Substitutions{}
	return dNode.retrieveRec(seq, Env)
}

func (dNode DiscriminationNode) retrieveRec(seq []SymbolType, currentEnv subst.Substitutions) []CandidatResult {

	ch := make(chan []CandidatResult)
	var results []CandidatResult

	var wg sync.WaitGroup

	if len(seq) == 0 { // End of recursion

		for _, p := range dNode.getLeafFor().GetSlice() {
			results = append(results, MakeCandidat(p, currentEnv))
		}
		return results
	}

	// Work goroutine
	for _, child := range dNode.children.GetSlice() {

		wg.Add(1) // Create exactly 1 goroutine
		go retrieveCase(seq, currentEnv, child, ch, &wg)
	}

	// Main goroutine waiting until all the goroutine stop
	go func() {
		wg.Wait()
		close(ch)
	}()

	for matches := range ch {

		results = append(results, matches...)

	}

	return results
}

/*****************************/
/* DataStruct implementation */
/*****************************/

func (dNode DiscriminationNode) Print() {
	for _, child := range dNode.getChildren().GetSlice() {
		child.displayRec(2) // Magic Number (Set the indent but bellow 2 the display is horrible and above 2 is bugget for ??? reason)
	}
}

func (dNode DiscriminationNode) displayRec(indent int) {

	prefix := strings.Repeat("    ", indent-1) + " |-- "

	if indent == 2 {
		prefix = strings.Repeat("[ROOT]", indent-1) + " |-- "
	}
	debug(Lib.MkLazy(func() string {
		return fmt.Sprintf("%s%s arity : %d\n", prefix, dNode.getSymbol().ToString(), dNode.GetArity())
	}))

	if dNode.getLeafFor().Len() > 0 {
		leafPrefix := strings.Repeat("    ", indent) + " [=> "
		for _, pred := range dNode.getLeafFor().GetSlice() {
			debug(Lib.MkLazy(func() string {
				return fmt.Sprintf("%s%s]\n", leafPrefix, pred.ToString())
			}))
		}
	}
	for _, child := range dNode.getChildren().GetSlice() {
		child.displayRec(indent + 1)
	}
}

func (dNode DiscriminationNode) IsEmpty() bool {
	return dNode.symbol.IsNil()
}

func (dNode DiscriminationNode) Copy() subst.DataStructure {

	newChildMaster := Lib.NewList[DiscriminationNode]()
	for _, child := range dNode.getChildren().GetSlice() {
		newChild := child.Copy().(DiscriminationNode)
		newChildMaster.Append(newChild)
	}

	newLeafFor := Lib.ListCpy(dNode.getLeafFor())
	return DiscriminationNode{
		symbol:   dNode.symbol,
		children: newChildMaster,
		leafFor:  newLeafFor,
	}

}

func (dNode DiscriminationNode) MakeDataStruct(formulas Lib.List[AST.Form], is_pos bool) subst.DataStructure {

	form := Lib.NewList[AST.Form]()

	for _, f := range formulas.GetSlice() {
		switch nf := f.(type) {
		case AST.Pred:
			if is_pos {
				form.Append(nf.Copy())
			}
		case AST.Not:
			switch nf.GetForm().(type) {
			case AST.Pred:
				if !(is_pos) {
					form.Append(nf.GetForm())
				}
			}
		}
	}

	return dNode.InsertFormulaListToDataStructure(form)
}

func (dNode DiscriminationNode) InsertFormulaListToDataStructure(lf Lib.List[AST.Form]) subst.DataStructure {
	for _, f := range lf.GetSlice() {
		switch nf := f.Copy().(type) {
		case AST.Pred:
			dNode = dNode.Insert(nf)
		case AST.Not:
			switch newForm := nf.GetForm().(type) { // Get the type AST.Form
			case AST.Pred:
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

func (dNode DiscriminationNode) UnifyTerm(inputTerm AST.Term) (bool, []subst.MixedTermSubstitutions) {

	var mixed []subst.MixedTermSubstitutions
	var found bool
	tmpContext := NewContext()

	seq := parseTerm(inputTerm, tmpContext).GetSlice()
	candidates := dNode.retrieveRec(seq, subst.MakeEmptySubstitution())

	for _, possibleMatch := range candidates {

		candidateTerm := subst.TransformPred(possibleMatch.getPred())
		emptySubst := subst.Substitutions{}
		finalSubst := subst.AddUnification(inputTerm, candidateTerm, emptySubst) // Call Robinson

		if !finalSubst.Equals(subst.Failure()) {
			found = true
			mixMatch := subst.MixMatchSubstitutions{
				Tof:   Lib.MkLeft[AST.Term, AST.Form](inputTerm),
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
