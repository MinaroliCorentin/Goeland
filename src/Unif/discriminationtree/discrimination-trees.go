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
	"strings"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
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

func (t SymbolType) getArity() int {
	return t.arity
}

func (s SymbolType) IsEmpty() bool {
	return s.symbol == nil && s.arity == -1
}

/* Each node of a CodeTree is composed of a sequence of instruction and its children. If it's a leaf, it has formulaes corresponding to the sequence of instructions. */
type DiscriminationNode struct {
	// Unification tout du long
	symbol   SymbolType                               // Variable name or function name
	children Lib.List[DiscriminationNode]             // All the children of the node
	leafFor  Lib.List[Lib.Either[AST.Term, AST.Form]] // If not empty, contains the where it come from
}

// Basic Node with no data inside
func NewNode() DiscriminationNode {
	return DiscriminationNode{
		symbol:   SymbolType{symbol: nil, arity: -1},
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[Lib.Either[AST.Term, AST.Form]](),
	}
}

// Node with data
func MakeNodeWithId(id AST.Id, arity int) DiscriminationNode {
	return DiscriminationNode{
		symbol:   SymbolType{symbol: id, arity: arity},
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[Lib.Either[AST.Term, AST.Form]](),
	}
}

// Arity is 0 because it's a variable
func MakeNodeWithMeta(meta AST.Meta) DiscriminationNode {
	return DiscriminationNode{
		symbol:   SymbolType{symbol: meta, arity: 0},
		children: Lib.NewList[DiscriminationNode](),
		leafFor:  Lib.NewList[Lib.Either[AST.Term, AST.Form]](),
	}
}

func (dNode DiscriminationNode) isConstant() bool {
	return dNode.symbol.getArity() == 0
}

func (dNode DiscriminationNode) getArity() int {
	return dNode.symbol.getArity()
}

func (dNode DiscriminationNode) isLeaf() bool {
	return dNode.children.Len() == 0
}

func (dNode DiscriminationNode) getSymbol() AST.Term {
	return dNode.symbol.getSymbol()
}

func (dNode DiscriminationNode) isEmpty() bool {
	return dNode.symbol.IsEmpty()
}

func (dNode DiscriminationNode) isFun() bool {
	return dNode.symbol.getSymbol().IsFun()
}

func (dNode DiscriminationNode) isMeta() bool {
	return dNode.symbol.getSymbol().IsMeta()
}

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
		return DiscriminationNode{FirstElementToSymbolType(t), children, Lib.NewList[Lib.Either[AST.Term, AST.Form]]()}
	case AST.Meta:
		return DiscriminationNode{FirstElementToSymbolType(t), Lib.NewList[DiscriminationNode](), Lib.NewList[Lib.Either[AST.Term, AST.Form]]()}
	default:
		Glob.Anomaly("TermToST", "Var or Id")
		return NewNode()
	}
}

func (dNode DiscriminationNode) DisplayDiscriminationTree() string {
	return dNode.displayRec("")
}

func (dNode DiscriminationNode) displayRec(indent string) string {

	var b strings.Builder
	flag := 0

	// Print the node
	if dNode.isEmpty() {
		b.WriteString(indent + "[Root/Empty]\n")
	} else {
		sym := dNode.getSymbol()
		if sym != nil {
			b.WriteString(indent + "|-- " + sym.ToString() + "\n")
		}
	}
	// Call the children
	for _, child := range dNode.children.GetSlice() {
		if child.isMeta() {
			if flag == 1 {
				b.WriteString(child.displayRec(indent))
			} else {
				flag = 1
				b.WriteString(child.displayRec(indent + "    "))
			}
		} else {
			flag = 0
			b.WriteString(child.displayRec(indent + "    "))
		}
	}

	return b.String()
}

// Parser for a formula : f(a) -> [f,a]
func SequenceParser(t AST.Term) []AST.Term {

	seq := []AST.Term{t} // Add the node before recursive call

	switch term := t.(type) {
	case AST.Fun: // Add all the args of the function
		for _, arg := range term.GetArgs().GetSlice() {
			seq = append(seq, SequenceParser(arg)...)
		}
	}

	return seq
}

func (s SymbolType) Equals(target SymbolType) bool {

	// If the arity is different, no need to go further
	if s.arity != target.arity {
		return false
	}

	// call sig.Equals
	return s.symbol.Equals(target.symbol)
}

func (dNode DiscriminationNode) Insert(t AST.Term) DiscriminationNode {
	seq := SequenceParser(t)
	return dNode.insertRec(seq, t)
}

func (dNode DiscriminationNode) insertRec(seq []AST.Term, originalTerm AST.Term) DiscriminationNode {
	// End of recursion, time to insert
	if len(seq) == 0 {
		dNode.leafFor.Append(Lib.MkLeft[AST.Term, AST.Form](originalTerm))
		return dNode
	}

	// Create Symbol
	sym := FirstElementToSymbolType(seq[0])
	foundIndex := -1
	childrenSlice := dNode.children.GetSlice()

	// Looking for already existing child
	for i, child := range childrenSlice {
		if child.symbol.Equals(sym) {
			foundIndex = i // If we find a match we can end this loop
			break
		}
	}

	// Child already exist
	if foundIndex != -1 {
		// Insert and update the sequence
		updatedChild := childrenSlice[foundIndex].insertRec(seq[1:], originalTerm)
		dNode.children.Upd(foundIndex, updatedChild)

		// Child doesn't exist
	} else {
		// Create new Child
		newChild := DiscriminationNode{
			symbol:   sym,
			children: Lib.NewList[DiscriminationNode](),
			leafFor:  Lib.NewList[Lib.Either[AST.Term, AST.Form]](),
		}
		updatedChild := newChild.insertRec(seq[1:], originalTerm) // Insert the rest of the sequence after the new child
		dNode.children.Append(updatedChild)                       // Update the children of the args node
	}
	return dNode // Return updated node
}
