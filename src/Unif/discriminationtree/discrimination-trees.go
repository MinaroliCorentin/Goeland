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

type NodeElement interface {
	ToString() string
	isAllowedNodeElement()
	IsMeta() bool
	GetArityType() int
	GetTy() AST.Ty
	Equals(target NodeElement) bool
}

func (ns NodeString) ToString() string {
	return string(ns)
}

type NodeString string
type TermNode struct{ AST.Term }
type TyNode struct{ AST.Ty }

func (ns NodeString) isAllowedNodeElement() {}
func (tn TermNode) isAllowedNodeElement()   {}
func (tn TyNode) isAllowedNodeElement()     {}

func (ns NodeString) IsMeta() bool {
	return false
}

func (tn TermNode) IsMeta() bool {
	return tn.Term.IsMeta()
}

func (tn TyNode) IsMeta() bool {
	return false
}

func (ns NodeString) GetArityType() int {
	return 0
}

func (tn TermNode) GetArityType() int {
	return tn.GetMetaList().Len()
}

func (tn TyNode) GetArityType() int {
	return 0
}

func (sym SymbolType) getTerm() AST.Term {

	if tn, ok := sym.symbol.(TermNode); ok {
		return tn.Term
	}
	return nil

}

func (sym SymbolType) GetTy() AST.Ty {

	if tn, ok := sym.symbol.(TyNode); ok {
		return tn.Ty
	}
	return nil

}

func (sym SymbolType) getString() string {

	if ns, ok := sym.symbol.(NodeString); ok {
		return ns.ToString()
	}
	return ""
}

func (ns NodeString) Equals(target NodeElement) bool {

	typ, ok := target.(NodeString)
	if !ok {
		return false
	}
	return strings.EqualFold(ns.ToString(), typ.ToString())
}

func (tn TermNode) Equals(target NodeElement) bool {
	typ, ok := target.(TermNode)
	if !ok {
		return false
	}

	res := tn.Term.Equals(typ.Term)
	if !res {
		fmt.Println("--- EQUALS FAILED ---")
		fmt.Printf("%s | Type : %T\n", tn.Term.ToString(), tn.Term)
		fmt.Printf("%s | Type: %T\n", typ.Term.ToString(), typ.Term)
		fmt.Println("---------------------")
	}

	return res
}
func (tn TyNode) Equals(target NodeElement) bool {

	typ, ok := target.(TyNode)
	if !ok {
		return false
	}
	return tn.Ty.Equals(typ.Ty)
}

func (ns NodeString) GetTy() AST.Ty {

	return AST.TIndividual() // Temporary

}

func (tn TermNode) GetTy() AST.Ty {

	return tn.ToMeta().GetTy()

}

func (tn TyNode) GetTy() AST.Ty {

	return tn.Ty

}

func createNodeElement(t any) NodeElement {

	switch v := t.(type) {
	case string:
		return NodeString(v)
	case AST.Ty:
		return TyNode{v}
	case AST.Pred:
		return TermNode{subst.TransformPred(v)}
	case AST.Term:
		return TermNode{v}
	default:
		Glob.Anomaly("Unknow Type from createNodeElement(t any) NodeElement ", "Unknow Type from createNodeElement(t any) NodeElement")
		return nil
	}
}

type SymbolType struct {
	symbol NodeElement // Term of the node
	arity  int         // Arity of a node
}

func (t SymbolType) ToString() string {
	return fmt.Sprintf("Symbol : %s Arity :  %d\n", t.symbol.ToString(), t.GetArity())
}

func (t SymbolType) getSymbol() NodeElement {
	return t.symbol
}

func (t SymbolType) GetArity() int {
	return t.arity
}

func (s SymbolType) IsNil() bool {
	return s.symbol == nil && s.arity == -1
}

func makeSymbolTypeTy(node NodeElement) SymbolType {
	return SymbolType{node, 0}
}

func makeSymbolType(node NodeElement, arity int) SymbolType {

	return SymbolType{node, arity}
}

// Equals between two SymbolType
func (s SymbolType) Equals(target SymbolType) bool {

	if s.GetArity() != target.GetArity() {
		return false
	}

	return s.symbol.Equals(target.symbol)
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
func MakeDiscriminationNodeWithSym(sym SymbolType) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

// Basic Node with SymbolType, children and empty List for leafFor
func MakeDiscriminationNodeWithSymAndChildren(sym SymbolType, children Lib.List[DiscriminationNode]) DiscriminationNode {
	return DiscriminationNode{
		symbol:   sym,
		children: children,
		leafFor:  Lib.NewList[AST.Pred](),
	}
}

func (dNode DiscriminationNode) getSymbol() SymbolType {
	return dNode.symbol
}

func (dNode DiscriminationNode) GetArity() int {
	return dNode.symbol.GetArity()
}

func (dNode DiscriminationNode) getElement() any {
	return dNode.getSymbol().getSymbol()
}

func (dNode DiscriminationNode) getChildren() Lib.List[DiscriminationNode] {
	return dNode.children
}

func (dNode DiscriminationNode) getLeafFor() Lib.List[AST.Pred] {
	return dNode.leafFor
}

func (dNode DiscriminationNode) toString() string {

	if dNode.getSymbol().getSymbol() == nil {
		Glob.Anomaly("Symbol is Nil", "Symbol is nil")
		return ""
	}
	return dNode.getSymbol().getSymbol().ToString()

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

func (Candidat CandidatResult) toString() string {
	return fmt.Sprintf("Pred : %s Subs :  %s\n", Candidat.getPred().ToString(), Candidat.GetSubs().ToString())
}

// Works only if Len(CandidatResult) is 1. Had Enough to for-each all the time for single element
func ToSingleElement(candidats []CandidatResult) CandidatResult {
	if len(candidats) == 1 {
		return candidats[0]
	}
	return CandidatResult{}
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

func parseTerm(t AST.Term, ctx *NormalizerContext) Lib.List[SymbolType] {

	res := Lib.NewList[SymbolType]()

	termTy := t.ToMeta().GetTy()
	res.Append(makeSymbolTypeTy(createNodeElement(termTy)))

	switch term := t.(type) {

	// if term is a function or cst, add and call his args
	case AST.Fun:

		funSansArgs := AST.MakerFun(term.GetID(), term.GetTyArgs(), Lib.NewList[AST.Term]())
		first_element := makeSymbolType(createNodeElement(funSansArgs), term.GetArgs().Len())
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

		normalizedMeta := ctx.mapping[originalName]                      // Return the transformed name association to the originalName before adding
		res.Append(makeSymbolType(createNodeElement(normalizedMeta), 0)) // Add the new Meta to the return slice

	case AST.Id:
		funSansArgs := AST.MakerFun(term, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
		first_element := makeSymbolType(createNodeElement(funSansArgs), 0)
		res.Append(first_element)

	default:
		Glob.Anomaly("Error with %s in ParseTerm", term.GetName())
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
// Case t is a cst => SymbolType{MakerFun(t.ID), 0}
// Case t is a Meta => SymbolType{t.ID, 0}
// Else Glob.Anomaly
func FirstElementToSymbolType(t AST.Term) SymbolType {

	switch t := t.(type) {
	case AST.Fun: // Case function
		funSansArgs := AST.MakerFun(t.GetID(), t.GetTyArgs(), Lib.NewList[AST.Term]())
		return SymbolType{createNodeElement(funSansArgs), t.GetArgs().Len()}
	case AST.Id:
		funSansArgs := AST.MakerFun(t, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
		return SymbolType{createNodeElement(funSansArgs), 0}
	case AST.Meta: // Case metaVariable
		return SymbolType{createNodeElement(t), 0}
	default: // Not supposed to see something else
		Glob.Anomaly("FirstElementToSymbolType Error", "Unknow type in FirstElementToSymbolType")
		return SymbolType{createNodeElement(nil), -1} // Dog Code that will fail but won't be triggered due to Glob.Anomaly. Only here to please the compiler.
	}
}

// Depend of the Type, create the follow DiscriminationNode
// case AST.Fun => Create a List and fill it with TermToNode(GetArgs) then Maker DiscrmiminationNode
// Case AST.Id => MakeDiscriminationNode(FirstElementToSymbol) => Create Fun
// Case AST.Meta => MakeDiscriminationNode(FirstElementToSymbol) => Create Meta
func TermToNode(t AST.Term) DiscriminationNode {
	switch t := t.(type) {
	case AST.Fun: // Accumulate all the term of the AST.Term then create a Node with all the children
		children := Lib.NewList[DiscriminationNode]()
		for _, c := range t.GetArgs().GetSlice() {
			children.Append(TermToNode(c))
		}
		return MakeDiscriminationNodeWithSymAndChildren(FirstElementToSymbolType(t), children)
	case AST.Id:
		return MakeDiscriminationNodeWithSym(FirstElementToSymbolType(t))
	case AST.Meta: // Node with T as SymbolType and empty children / leafFor
		return MakeDiscriminationNodeWithSym(FirstElementToSymbolType(t))
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

// Predicat Parser. Skip the Predicat Type and Transform it into a Function.
// Then Call parseTerm on the args of the predicat.
func parsePred(p AST.Pred, ctx *NormalizerContext) Lib.List[SymbolType] {

	res := Lib.NewList[SymbolType]()

	// Required Overwise the SymbolType of the predicat will be AST.ID and will be compared with a AST.Fun -> Automatic faillure
	tmpFun := AST.MakerFun(p.GetID(), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
	res.Append(makeSymbolType(createNodeElement(tmpFun), p.GetArgs().Len()))

	for _, arg := range p.GetArgs().GetSlice() {
		res.Append(parseTerm(arg, ctx).GetSlice()...)
	}

	return res
}

// Insert a AST.Pred in the tree. If using a AST.Form or Something Else, it have to be cast when inserting ( tree = tree.Insert(px.(AST.pred)) )
// Call the parser then the auxiliary function
func (dNode DiscriminationNode) Insert(p AST.Pred) DiscriminationNode {

	sym_list := parsePred(p, NewContext())
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
	var ok = false

	// Looking for already existing child
	for i, child := range childrenSlice {
		if child.getSymbol().getSymbol().Equals(sym.getSymbol()) {
			if child.GetArity() == sym.GetArity() {
				foundIndex = i
				ok = true
				break
			} else {
				Glob.Anomaly("Arity Missmatch", "Same Symbol but different Arity")
			}

		}
	}

	if ok { // Child already exist

		// Insert and update the sequence
		updatedChild := childrenSlice[foundIndex].insertRec(seq.RemoveAt(0), originalTerm)
		dNode.children.Upd(foundIndex, updatedChild) // Update children[foundIntex] = updateChild

	} else { // if Child doesn't exist

		newChild := MakeDiscriminationNodeWithSym(sym)                    // Create a new Node with the new SymbolType and his leafFor
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

	needed := 1 // Type + Term
	index := 0

	for needed > 0 && index < len(seq) {
		sym := seq[index]
		arite := sym.GetArity()

		if arite > 0 {
			arite = arite * 2
		}

		needed = needed - 1 + arite // If Arity == 0 ( Meta ) end this loop, else add the arity of the form/func/...
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

		arite := child.GetArity()
		if arite > 0 {
			arite = arite * 2 // Each Type + Term
		}

		newNeeded := needed - 1 + arite // 0 if Meta, Else Arity of the Term
		matches := child.SkipTreeTermAndContinue(newNeeded, remainingQuery, substitutions)
		subs = append(subs, matches...)
	}
	return subs

}

func (dNode DiscriminationNode) RetrieveUnifiables(t AST.Form) []CandidatResult {
	predFormula, _ := t.(AST.Pred)
	seq := parsePred(predFormula, NewContext()).GetSlice()
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

func retrieveCase(seq []SymbolType, currentEnv subst.Substitutions, child DiscriminationNode, ch chan<- []CandidatResult, wg *sync.WaitGroup) {

	defer wg.Done()

	symQuery := seq[0]            // First Element
	childSym := child.getSymbol() // child is meta or cst

	isExactMatch := child.symbol.Equals(symQuery)
	if isExactMatch { // Exact Match
		matches := child.retrieveRec(seq[1:], currentEnv) // Exact Match -> Search next element
		ch <- matches
	}

	// Case the child is a AST.Meta
	if child.getSymbol().getSymbol().IsMeta() && !isExactMatch {

		// We noticed that the term of the dNode is a Meta
		// Meaning that we can skip the current term of the seq ( paramater of this function ) because it will be unify with the current term
		// e.g dNode = x, seq = [f,a] so [f,a] |-> x and we skip 2 because GetSbTermLength of [f,a] is 2
		skip := GetSubTermLength(seq)

		if skip <= len(seq) { // Security to prevent segfault

			var mergedSub subst.Substitutions
			if skip == 1 {
				currentSub := subst.MakeSubstitution(childSym.getTerm().ToMeta(), symQuery.getTerm())
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

	} else if symQuery.getSymbol().IsMeta() && !isExactMatch {

		// Reverse of the situation with the previous if.
		// The symbol from seq ( parameter of this function ) is a Meta, meaning we skip the current term of dNode because it will be unify
		// e.g dNode = a, seq = [x] so a |-> x and we got to the next term of the dNode

		var mergedSub subst.Substitutions

		if child.GetArity() == 0 {
			currentSub := subst.MakeSubstitution(symQuery.getTerm().ToMeta(), childSym.getTerm()) // Create a new substitution
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

			tokensToSkip := child.GetArity()
			if tokensToSkip > 0 {
				tokensToSkip = tokensToSkip * 2
			}

			childResults := child.SkipTreeTermAndContinue(tokensToSkip, seq[1:], mergedSub)
			ch <- childResults
		}

	} else {
		// No recursive call or return
	}

}

/*****************************/
/* DataStruct implementation */
/*****************************/

func (dNode DiscriminationNode) Print() {
	if dNode.IsEmpty() {
		fmt.Println("Empty Tree")
		return
	}
	fmt.Println("[ROOT]")
	for _, child := range dNode.getChildren().GetSlice() {
		child.displayRec(1)
	}
}

func (dNode DiscriminationNode) displayRec(depth int) {

	indent := strings.Repeat("    ", depth)

	var nodeTag string

	switch dNode.getSymbol().getSymbol().(type) {
	case TyNode:
		nodeTag = "[Ty]"
	case TermNode:
		nodeTag = "[Term]"
	case NodeString:
		nodeTag = "[String]"
	}

	fmt.Printf("%s|-- %s %s (arity: %d)\n", indent, nodeTag, dNode.toString(), dNode.GetArity())

	if dNode.getLeafFor().Len() > 0 {
		leafIndent := indent + "    "
		for _, pred := range dNode.getLeafFor().GetSlice() {
			fmt.Printf("%s[=> %s]\n", leafIndent, pred.ToString())
		}
	}

	for _, child := range dNode.getChildren().GetSlice() {
		child.displayRec(depth + 1)
	}
}

func (dNode DiscriminationNode) IsEmpty() bool {
	return dNode.getChildren().Empty()
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
			matching := subst.MakeMatchingSubstitutions(possibleMatch.getPred(), finalSubst) // constructor
			mixed = append(mixed, matching.ToMixed())                                        // convert To Mixed for return
		}
	}
	return found, mixed
}

func (dNode DiscriminationNode) UnifyTerm(inputTerm AST.Term) (bool, []subst.MixedTermSubstitutions) {

	var mixed []subst.MixedTermSubstitutions
	var found bool
	tmpContext := NewContext()

	seq := parseTerm(inputTerm, tmpContext).GetSlice()

	// Remove the Initial $i
	var seq2 []SymbolType
	for i, elem := range seq {
		if i > 0 {
			seq2 = append(seq2, elem)
		}
	}

	candidates := dNode.retrieveRec(seq2, subst.MakeEmptySubstitution())
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

///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////
///////////////////////////////////////////////

func parsePred2(p AST.Pred) Lib.List[SymbolType] {

	res := Lib.NewList[SymbolType]()

	// Required Overwise the SymbolType of the predicat will be AST.ID and will be compared with a AST.Fun -> Automatic faillure
	tmpFun := AST.MakerFun(p.GetID(), Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
	res.Append(makeSymbolType(createNodeElement(tmpFun), p.GetArgs().Len()))

	fmt.Println("fun tmp (paramtre)", tmpFun.IsFun())

	for _, arg := range p.GetArgs().GetSlice() {
		res.Append(parseTerm2(arg).GetSlice()...)
	}

	return res
}

func parseTerm2(t AST.Term) Lib.List[SymbolType] {

	res := Lib.NewList[SymbolType]()

	termTy := t.ToMeta().GetTy()
	res.Append(makeSymbolTypeTy(createNodeElement(termTy)))

	switch term := t.(type) {

	// if term is a function or cst, add and call his args
	case AST.Fun:

		funSansArgs := AST.MakerFun(term.GetID(), term.GetTyArgs(), Lib.NewList[AST.Term]())
		first_element := makeSymbolType(createNodeElement(funSansArgs), term.GetArgs().Len())
		res.Append(first_element)
		for _, arg := range term.GetArgs().GetSlice() {
			res.Append(parseTerm2(arg).GetSlice()...)
		}

	// Case meta, we have to transform it
	case AST.Meta:

		res.Append(makeSymbolType(createNodeElement(term), 0)) // Add the new Meta to the return slice

	case AST.Id:

		funSansArgs := AST.MakerFun(term, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
		first_element := makeSymbolType(createNodeElement(funSansArgs), 0)
		res.Append(first_element)

	default:
		Glob.Anomaly("Error with %s in ParseTerm2", term.GetName())
	}
	return res

}

func (dNode DiscriminationNode) SkipTreeTermAndContinue2(needed int, remainingQuery []SymbolType, substitutions subst.Substitutions) []CandidatResult {
	var subs []CandidatResult

	// End of recursion
	if needed == 0 {
		return dNode.retrieveRec2(remainingQuery, substitutions)
	}

	for _, child := range dNode.getChildren().GetSlice() {
		arite := child.GetArity()
		if arite > 0 {
			arite = arite * 2
		}

		newNeeded := needed - 1 + arite
		matches := child.SkipTreeTermAndContinue2(newNeeded, remainingQuery, substitutions)
		subs = append(subs, matches...)
	}
	return subs
}

func (dNode DiscriminationNode) Unify2(inputFormula AST.Form) (bool, []subst.MixedSubstitutions) {

	dNode.Print()
	fmt.Println("inputFOrmula", inputFormula.ToString())

	candidates := dNode.RetrieveUnifiables2(inputFormula)
	var mixed []subst.MixedSubstitutions
	var found bool

	fmt.Println("Len Candidates", len(candidates))

	queryPred, isQueryPred := inputFormula.(AST.Pred)
	if !isQueryPred {
		return false, mixed
	}

	for _, possibleMatch := range candidates {

		fmt.Println("Execution Candidates")

		candPred := possibleMatch.getPred()

		if !queryPred.GetID().Equals(candPred.GetID()) {
			continue
		}

		argsQuery := queryPred.GetArgs().GetSlice()
		argsCand := candPred.GetArgs().GetSlice()
		if len(argsQuery) != len(argsCand) {
			continue
		}

		currentEnv := subst.Substitutions{}
		isUnifiable := true

		for i := 0; i < len(argsQuery); i++ {
			currentEnv = subst.AddUnification(argsQuery[i], argsCand[i], currentEnv)
			if currentEnv.Equals(subst.Failure()) {
				isUnifiable = false
				break
			}
		}

		if isUnifiable {
			found = true
			matching := subst.MakeMatchingSubstitutions(inputFormula, currentEnv)
			mixed = append(mixed, matching.ToMixed())
		}
	}

	return found, mixed
}

func (dNode DiscriminationNode) UnifyTerm2(inputTerm AST.Term) (bool, []subst.MixedTermSubstitutions) {
	var mixed []subst.MixedTermSubstitutions
	var found bool

	seq := parseTerm2(inputTerm).GetSlice()

	if len(seq) > 0 {
		if _, isTy := seq[0].getSymbol().(TyNode); isTy {
			seq = seq[1:]
		}
	}

	for _, elem := range seq {
		fmt.Println("elem : ", elem.ToString())
		fmt.Println("Type : ", elem.getSymbol().GetTy().ToString())
	}

	candidates := dNode.retrieveRec2(seq, subst.MakeEmptySubstitution())

	for _, possibleMatch := range candidates {

		fmt.Println("Candidates", possibleMatch.toString())

		currentSubst := possibleMatch.GetSubs()
		candidateTerm := subst.TransformPred(possibleMatch.getPred()) // Pred -> Term

		finalSubst := subst.AddUnification(inputTerm, candidateTerm, currentSubst)

		if !finalSubst.Equals(subst.Failure()) {
			found = true
			mixMatch := subst.MixMatchSubstitutions{
				Tof:   Lib.MkLeft[AST.Term, AST.Form](inputTerm),
				Subst: finalSubst,
			}
			mixed = append(mixed, mixMatch.ToMixedTerm())
		}
	}
	return found, mixed
}

// Take a Sequence of SymbolType and return the first AST.Term + the remaining sequence
func ReconstructTerm(seq []SymbolType) (AST.Term, []SymbolType) {

	if len(seq) == 0 {
		return nil, seq
	}
	index := 0

	if _, ok := seq[index].getSymbol().(TyNode); ok {
		index++
	}
	if index >= len(seq) {
		return nil, seq[index:]
	}

	head := seq[index]
	arite := head.GetArity()
	term := head.getTerm()
	index++

	switch t := term.(type) {

	case AST.Fun:

		currentSeq := seq[index:]
		args := Lib.NewList[AST.Term]()
		for i := 0; i < arite; i++ {
			var arg AST.Term
			arg, currentSeq = ReconstructTerm(currentSeq)
			args.Append(arg)
		}
		return AST.MakerFun(t.GetID(), t.GetTyArgs(), args), currentSeq // Create Fun

	case AST.Meta:
		return t, seq[index:] // Go next
	case AST.Id:
		return AST.MakerFun(t, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]()), seq[index:]
	default:
		return nil, seq[index:] // Error type
	}
}

func (dNode DiscriminationNode) RetrieveUnifiables2(t AST.Form) []CandidatResult {
	predFormula, _ := t.(AST.Pred)

	seq := parsePred2(predFormula).GetSlice()
	Env := subst.Substitutions{}

	for _, elem := range seq {
		fmt.Println("ParsePred2", elem.ToString())
	}

	return dNode.retrieveRec2(seq, Env)
}

func (dNode DiscriminationNode) retrieveRec2(seq []SymbolType, currentEnv subst.Substitutions) []CandidatResult {

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
		go retrieveCase2(seq, currentEnv, child, ch, &wg)
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

func retrieveCase2(seq []SymbolType, currentEnv subst.Substitutions, child DiscriminationNode, ch chan<- []CandidatResult, wg *sync.WaitGroup) {

	defer wg.Done()
	symQuery := seq[0] // First Element
	isExactMatch := child.symbol.Equals(symQuery)
	if isExactMatch { // Exact Match
		matches := child.retrieveRec2(seq[1:], currentEnv) // Exact Match -> Search next element
		ch <- matches
	}
	childSym := child.getSymbol() // child is meta or cst

	// We noticed that the term of the dNode is a Meta
	// Meaning that we can skip the current term of the seq ( paramater of this function ) bc it will be unify with the current term
	// e.g dNode = x, seq = [f,a] so [f,a] |-> x and we skip 2 because GetSbTermLength of [f,a] is 2
	if childSym.getSymbol().IsMeta() && !isExactMatch {

		fmt.Println("ChildSym Symbol", childSym.getSymbol().ToString())

		queryTerm, restSeq := ReconstructTerm(seq)
		if queryTerm != nil {
			fmt.Println("QueryTerm not null")
			mergedSub := subst.AddUnification(childSym.getTerm(), queryTerm, currentEnv) // Robinson Call
			if !mergedSub.Equals(subst.Failure()) {
				fmt.Println("MergeSub reussit")
				matches := child.retrieveRec2(restSeq, mergedSub)

				for _, elem := range matches {
					fmt.Println("matches", elem.getPred().ToString())
				}

				ch <- matches
			} else {
				fmt.Println("MergeSub Failure")
			}
		}

	} else if symQuery.getSymbol().IsMeta() && !isExactMatch {

		fmt.Println("symQuery Symbol", symQuery.getSymbol().ToString())

		var mergedSub subst.Substitutions
		if child.GetArity() == 0 {

			// Case 1: The tree contains a constant (arity 0).
			// We have the full term right here, so we can immediately bind the Query's Meta variable
			// to this constant and update our substitution environment.
			childTerm := childSym.getTerm()
			var properTerm AST.Term = childTerm

			// If for ??? reason it's a AST.id, we transform it to AST.Fun ( Tmp? )
			if id, ok := childTerm.(AST.Id); ok {
				properTerm = AST.MakerFun(id, Lib.NewList[AST.Ty](), Lib.NewList[AST.Term]())
			}

			currentSub := subst.MakeSubstitution(symQuery.getTerm().ToMeta(), properTerm)
			tmp3 := subst.Substitutions{currentSub}
			if len(currentEnv) == 0 {
				mergedSub = tmp3
			} else {
				mergedSub, _ = subst.MergeSubstitutions(currentEnv, tmp3)
			}
		} else {
			// Case 2: The tree contains a function with arity > 0.
			// At this node, we only see the function symbol, not its arguments (which live deeper in the tree).
			// To avoid sending an incomplete term to Robinson, we DEFER the unification of this Meta variable.
			// We pass the current environment as-is, allowing the recursion to consume all the function's
			// arguments further down the branch before finally binding the complete structural term.
			mergedSub = currentEnv
		}

		if !mergedSub.Equals(subst.Failure()) {
			tokensToSkip := child.GetArity()
			if tokensToSkip > 0 {
				tokensToSkip = tokensToSkip * 2 // Type + Term
			}
			childResults := child.SkipTreeTermAndContinue2(tokensToSkip, seq[1:], mergedSub)
			ch <- childResults
		}

	} // No recursive call or return
}
