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

package discriminationtree

import (
	"fmt"
	"log"
	"os"
	"testing"
	"time"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Typing"
	subst "github.com/GoelandProver/Goeland/Unif/substitution"
)

// Code trees
//var tp, tn Unif.DataStructure

// Id
var p_id AST.Id
var g_id AST.Id
var f_id AST.Id
var a_id AST.Id
var b_id AST.Id
var c_id AST.Id
var d_id AST.Id
var c1_id AST.Id
var c2_id AST.Id
var PR_id AST.Id

// Meta
var x AST.Meta
var y AST.Meta
var z AST.Meta
var z1 AST.Meta
var z2 AST.Meta
var z3 AST.Meta

// Const
var a AST.Fun
var b AST.Fun
var c AST.Fun
var d AST.Fun
var c1 AST.Fun
var c2 AST.Fun

// Fun
var gx AST.Fun
var ga AST.Fun
var fx AST.Fun
var fy AST.Fun
var fa AST.Fun
var fb AST.Fun
var fc AST.Fun

var ggx AST.Fun
var gga AST.Fun
var gfy AST.Fun
var gfa AST.Fun
var fxy AST.Fun
var fyz AST.Fun
var ffx AST.Fun
var fxa AST.Fun
var fay AST.Fun
var fab AST.Fun
var fbc AST.Fun
var fcd AST.Fun

var gggx AST.Fun

var f_fxy_z AST.Fun
var f_x_fyz AST.Fun
var f_fab_c AST.Fun
var f_a_fbc AST.Fun

// // Equalities
// var eq_x_y AST.Pred
// var eq_x_a AST.Pred
// var eq_y_a AST.Pred
// var eq_z1_c1 AST.Pred
// var eq_z1_c2 AST.Pred
// var eq_z2_c1 AST.Pred
// var eq_z3_c1 AST.Pred
// var eq_gx_fx AST.Pred
// var eq_ggx_fa AST.Pred
// var eq_gfy_y AST.Pred
// var eq_fa_a AST.Pred
// var eq_b_c AST.Pred
// var eq_a_b AST.Pred
// var eq_a_c AST.Pred
// var eq_b_d AST.Pred
// var eq_x_d AST.Pred

// // Inequalites
// var neq_x_a AST.Form
// var neq_a_b AST.Form
// var neq_a_d AST.Form
// var neq_gggx_x AST.Form
// var neq_fx_a AST.Form
// var neq_fx_x AST.Form
// var neq_fab_fcd AST.Form
// var neq_fb_fc AST.Form

// Form
var pggab AST.Form
var not_pac AST.Form
var pa AST.Form
var pb AST.Form

var not_pc AST.Form
var pab AST.Form
var pabc AST.Form
var pba AST.Form

var pca AST.Form
var pax AST.Form
var pay AST.Form
var pxy AST.Form
var pxx AST.Form
var px AST.Form
var py AST.Form
var pxc AST.Form
var pfx AST.Form
var pafx AST.Form
var pafy AST.Form
var pfac AST.Form

var not_pcd AST.Form

var PRa AST.Form
var PRb AST.Form

func initTestVariable() {
	// Id
	p_id = AST.MakerId("P")
	g_id = AST.MakerId("g")
	f_id = AST.MakerId("f")
	a_id = AST.MakerId("a")
	b_id = AST.MakerId("b")
	c_id = AST.MakerId("c")
	d_id = AST.MakerId("d")
	c1_id = AST.MakerId("c1")
	c2_id = AST.MakerId("c2")
	PR_id = AST.MakerId("PR")

	// Meta
	x = AST.MakerMeta("X", -1, AST.TIndividual())
	y = AST.MakerMeta("Y", -1, AST.TIndividual())
	z = AST.MakerMeta("Z", -1, AST.TIndividual())
	z1 = AST.MakerMeta("Z1", -1, AST.TIndividual())
	z2 = AST.MakerMeta("Z2", -1, AST.TIndividual())
	z3 = AST.MakerMeta("Z3", -1, AST.TIndividual())

	// Const
	a = AST.MakerConst(a_id)
	b = AST.MakerConst(b_id)
	c = AST.MakerConst(c_id)
	d = AST.MakerConst(d_id)
	c1 = AST.MakerConst(c1_id)
	c2 = AST.MakerConst(c2_id)

	// Fun
	gx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))
	ga = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	fx = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y))
	fa = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	fb = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	fc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c))

	ggx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gx))
	gga = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ga))
	gfy = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fy))
	gfa = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa))
	fxy = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y))
	fyz = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, z))
	ffx = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx))

	fxa = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, a))
	fay = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, y))
	fab = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	fbc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, c))
	fcd = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d))
	gggx = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](ggx))
	f_fxy_z = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fxy, z))
	f_x_fyz = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, fyz))
	f_fab_c = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fab, c))
	f_a_fbc = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fbc))

	// Predicates
	pggab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gga, b))
	not_pac = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, c)))
	not_pc = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c)))
	pab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	pabc = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b, c))
	pba = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, a))
	pca = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, a))
	pax = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, x))
	pay = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, y))
	pxy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y))
	pxx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, x))
	px = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x))
	py = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y))
	pxc = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, c))
	pfx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx))
	pafy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fy))
	pafx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fx))
	pfac = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa, c))
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d)))
	pa = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	pb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	PRa = AST.MakerPred(PR_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	PRb = AST.MakerPred(PR_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
}

func initDebuggers() {
	AST.InitDebugger()
	Typing.InitDebugger()
	subst.InitDebugger()
}

func TestMain(m *testing.M) {
	Glob.SetStart(time.Now())
	initDebuggers()
	AST.Init()
	Typing.Init()
	initTestVariable()
	Glob.EnableDebug()
	code := m.Run()
	os.Exit(code)
}

func TestFirstElementToSymbolType(t *testing.T) {

	tree := NewNode() // NewNode create a symbolType with arity == -1. Arity will be 0 if create normaly -> lead to false negative
	argsA := pa.GetSubTerms()
	termA := argsA.At(0)
	resultA := FirstElementToSymbolType(termA)
	tree.setSymbol(resultA)

	if tree.GetArity() == -1 {
		Glob.Anomaly("Arity Error", "Wrong Arity")
	} else {
		fmt.Println("OK")
	}

	tree2 := NewNode()
	argsB := pb.GetSubTerms()
	termB := argsB.At(0)
	resultB := FirstElementToSymbolType(termB)
	tree2.setSymbol(resultB)

	if tree2.GetArity() == -1 {
		Glob.Anomaly("Arity Error", "Wrong Arity")
	} else {
		fmt.Println("OK")
	}

	argsC := gga.GetArgs()
	resultC := FirstElementToSymbolType(argsC.At(0))
	if resultC.GetArity() == -1 {
		Glob.Anomaly("Arity Error", "Wrong Arity")
	} else {
		fmt.Println("OK")
	}

	fmt.Println("-----EXPECTED PANIC-----")
	func() {
		defer func() {
			if err := recover(); err != nil {
				log.Println("panic occurred:", err)
			} else {
				fmt.Println("Supposed to throw a Error")
			}
		}()

		argsD := c_id
		resultD := FirstElementToSymbolType(argsD)
		println("Not supposed to see this ", resultD.symbol) // Required or Go panic due variable not used. However if you see this print : Bon Courage

	}()
	fmt.Println("---END EXPECTED PANIC---")

}

func TestTermToNode(t *testing.T) {

	tree := NewNode()
	tree = TermToNode(ggx)
	tmp := tree.GetArity()

	if tmp != 1 {
		Glob.Anomaly("Element number", "Wrong number of element")
	}

	tree2 := NewNode()
	tree2 = TermToNode(fbc)
	tmp2 := tree2.GetArity()
	if tmp2 != 2 {
		Glob.Anomaly("Element number", "Wrong number of element")
	}
}

func TestInsert(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pba.(AST.Pred))
	tree = tree.Insert(pab.(AST.Pred))
	tree = tree.Insert(pafx.(AST.Pred))

	fmt.Println("-------------PANIC EXPECTED------------- ")
	func() {
		defer func() {
			if err := recover(); err != nil {
				log.Println("panic occurred:", err)
			}
		}()

		tree = tree.Insert(pabc.(AST.Pred)) // pabc supposed to throw a error
	}()
	fmt.Println("-----------END PANIC EXPECTED----------- ")
	tree.Print()

	println()
	println()
	println()

	tree2 := NewNode()
	tree2 = tree2.Insert(pfx.(AST.Pred))
	tree2.Print()

}

func TestPrintDiscriminationTree(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pa.(AST.Pred))
	tree = tree.Insert(pb.(AST.Pred))
	tree = tree.Insert(PRa.(AST.Pred))
	tree = tree.Insert(PRb.(AST.Pred))
	tree.Print()

	fmt.Println()
	fmt.Println()

	tree = tree.Insert(pa.(AST.Pred))
	tree.Print()
}

func TestPrintSamePredicatCheck(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pa.(AST.Pred))
	tree = tree.Insert(pb.(AST.Pred))
	tree = tree.Insert(PRa.(AST.Pred))
	tree = tree.Insert(PRb.(AST.Pred))
	tree.Print()

}

func TestPrintDoublonCheck(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pa.(AST.Pred))
	tree = tree.Insert(pa.(AST.Pred))
	tree.Print()

}

func TestParseFormula(t *testing.T) {

	tmp := parseFormula(pax)

	fmt.Println(tmp.GetSlice())

	for _, value := range tmp.GetSlice() {
		fmt.Println(value.getSymbol().ToString())
		if value.getSymbol().ToString() == "P" {
			if value.GetArity() != 2 {
				t.Fatalf("Arrity Error")
			}
		} else if value.getSymbol().ToString() == "a" {
			if value.GetArity() != 0 {
				t.Fatalf("Arrity Error")
			}
		} else if value.getSymbol().ToString() == "X" {
			if value.GetArity() != 0 {
				t.Fatalf("Arrity Error")
			}
		} else {
			t.Fatalf("Supposed to have only \"P\", \"a\" or \"X\" ")
		}
	}

	tmp2 := parseFormula(not_pac)
	for _, value := range tmp2.GetSlice() {
		fmt.Println(value.symbol.ToMeta())
	}

}

func TestParseTerm(t *testing.T) {

	var tmp []string
	var tmp2 []string
	var tmp3 []string

	seqList := parseTerm(fxy)
	seq := seqList.GetSlice()
	if len(seq) != 3 {
		t.Fatalf("Got %d elements", len(seq))
	}
	for _, sym := range seq {
		tmp = append(tmp, sym.getSymbol().ToString())
	}
	fmt.Printf(" Sequence Parsed : % v\n", tmp)

	seqList = parseTerm(f_fxy_z)
	seq = seqList.GetSlice()
	if len(seq) != 5 {
		t.Fatalf("Got %d elements", len(seq))
	}
	for _, sym := range seq {
		tmp2 = append(tmp2, sym.getSymbol().ToString())
	}
	fmt.Printf(" Sequence Parsed : %v\n", tmp2)

	seqList = parseTerm(f_x_fyz)
	seq = seqList.GetSlice()
	if len(seq) != 5 {
		t.Fatalf("Got %d elements", len(seq))
	}
	for _, sym := range seq {
		tmp3 = append(tmp3, sym.getSymbol().ToString())
	}
	fmt.Printf(" Sequence Parsed : %v\n", tmp3)

}

func TestRetrieve(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pax.(AST.Pred))
	tree = tree.Insert(pay.(AST.Pred))
	results := tree.RetrieveUnifiables(pab)
	if len(results) == 0 {
		t.Fatalf("Returned 0 element")
	} else {
		fmt.Printf("returned %d element", len(results))
	}

	for _, result := range results {
		fmt.Println("Pred : ", result.getPred().ToString())
		for _, element := range result.GetSubs() {
			fmt.Println("Subs : ", element.ToString())
		}
	}
	fmt.Println()

	tree2 := NewNode()
	tree2 = tree2.Insert(pax.(AST.Pred))
	results2 := tree2.RetrieveUnifiables(pba)
	if len(results2) != 0 {
		t.Fatalf(" Not supposed to have Unifiable element")
	}

	fmt.Println("----- EMPTY -----")
	fmt.Println("----- EMPTY -----")

	fmt.Println()

	tree3 := NewNode()
	tree3 = tree3.Insert(pxy.(AST.Pred))
	results3 := tree3.RetrieveUnifiables(pab)
	if len(results3) != 1 {
		t.Fatalf("Supposed to have 2 unifiables")
	}

	for _, result := range results3 {
		fmt.Println("Pred : ", result.getPred().ToString())
		for _, element := range result.GetSubs() {
			fmt.Println("Subs : ", element.ToString())
		}
	}

}

func TestEquals(t *testing.T) {

	ok := x.Equals(x)
	if !ok {
		t.Fatalf("Equals Test with failled")
	}

	ok2 := pxx.Equals(pxx)
	if !ok2 {
		t.Fatalf("Equals Test with failled")
	}

	ok3 := fab.Equals(fab)
	if !ok3 {
		t.Fatalf("Equals Test with failled")
	}

}

func TestGetSubTermLength(t *testing.T) {

	seq := parseTerm(ggx).GetSlice()
	var1 := (GetSubTermLength(seq))
	if var1 != 3 {
		t.Fatalf("Error SubTerLength with 2functions & 1Meta ")
	}

	seq2 := parseTerm(fxy).GetSlice()
	var2 := (GetSubTermLength(seq2))
	if var2 != 3 {
		t.Fatalf("Error SubTerLength with 1function & 2Meta")
	}

	seq3 := parseTerm(gx).GetSlice()
	var3 := (GetSubTermLength(seq3))
	if var3 != 2 {
		t.Fatalf("Error SubTerLength with 1function & 1Meta")
	}

	seq4 := parseTerm(ga).GetSlice()
	var4 := (GetSubTermLength(seq4))
	if var4 != 2 {
		t.Fatalf("Error SubTerLength with 1function & 1cst")
	}

	seq5 := parseTerm(gggx).GetSlice()
	var5 := (GetSubTermLength(seq5))
	if var5 != 4 {
		t.Fatalf("Error SubTerLength with 1function & 3Meta")
	}

}

func TestSkipTreeTermAndContinue(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pab.(AST.Pred))
	needed := 1
	emptyQuery := []SymbolType{}
	emptyEnv := subst.Substitutions{}
	results := tree.SkipTreeTermAndContinue(needed, emptyQuery, emptyEnv)
	if len(results) != 1 {
		t.Fatalf(" Expected 1 Element, got %d", len(results))
	}

	tree2 := NewNode()
	tree2 = tree2.Insert(px.(AST.Pred))
	needed2 := 1
	emptyQuery2 := []SymbolType{}
	emptyEnv2 := subst.Substitutions{}
	results2 := tree2.SkipTreeTermAndContinue(needed2, emptyQuery2, emptyEnv2)
	if len(results2) != 1 {
		t.Fatalf(" Expected 1 Element, got %d", len(results2))
	}

	tree3 := NewNode()
	tree3 = tree3.Insert(pba.(AST.Pred))
	tree3 = tree3.Insert(pab.(AST.Pred))
	needed3 := 1
	emptyQuery3 := []SymbolType{}
	emptyEnv3 := subst.Substitutions{}
	results3 := tree3.SkipTreeTermAndContinue(needed3, emptyQuery3, emptyEnv3)
	if len(results3) != 2 {
		t.Fatalf(" Expected 2 Element, got %d", len(results3))
	}

	tree4 := NewNode()
	tree4 = tree4.Insert(pba.(AST.Pred))
	tree4 = tree4.Insert(pab.(AST.Pred))
	tree4 = tree4.Insert(pca.(AST.Pred))
	needed4 := 1
	emptyQuery4 := []SymbolType{}
	emptyEnv4 := subst.Substitutions{}
	results4 := tree4.SkipTreeTermAndContinue(needed4, emptyQuery4, emptyEnv4)
	if len(results4) != 3 {
		t.Fatalf(" Expected 3 Element, got %d", len(results4))
	}

}

func TestRetrieveUnifiables(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pax.(AST.Pred))
	tree = tree.Insert(pba.(AST.Pred))
	candidat := tree.RetrieveUnifiables(pay)
	if len(candidat) != 1 {
		t.Fatalf("Should be only 1")
	}

	tree = tree.Insert(pafx.(AST.Pred))
	candidat = tree.RetrieveUnifiables(pay)
	if len(candidat) != 2 {
		t.Fatalf("Should be only 2")
	}

	tree = tree.Insert(pafy.(AST.Pred))
	candidat = tree.RetrieveUnifiables(pay)
	if len(candidat) != 3 {
		t.Fatalf("Should be only 3")
	}

	tree2 := NewNode()
	tree2 = tree2.Insert(pa.(AST.Pred))
	candidat2 := tree2.RetrieveUnifiables(pb)
	if len(candidat2) != 0 {
		t.Fatalf("Should be 0 because pa and pb can't be unified")
	}

}

func TestCopy(t *testing.T) {

	tree1 := NewNode()
	tree2 := tree1.Copy()
	tree1 = tree1.Insert(pax.(AST.Pred))
	res2 := tree2.IsEmpty()
	if !res2 {
		t.Fatalf("Tree2 is not a copy, it s only a pointer to tree1")
	}
}

func TestUnify(t *testing.T) {

	fmt.Println("-----TEST 01 -----")
	tree := NewNode()
	tree = tree.Insert(pax.(AST.Pred))
	var mix []subst.MixedSubstitutions
	_, mix = tree.Unify(pay)
	for _, elem := range mix {
		fmt.Println(elem.ToString())
	}
	if len(mix) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix {
		if elem.GetForm().ToString() != "P(a, Y)" {
			t.Fatalf("Fatal Failure, shouhd have P(a, Y)")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 02 -----")
	tree1 := NewNode()
	tree1 = tree1.Insert(pax.(AST.Pred))
	var mix1 []subst.MixedSubstitutions
	_, mix1 = tree1.Unify(pab)
	for _, elem := range mix1 {
		fmt.Println(elem.ToString())
	}
	if len(mix1) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix1 {
		if elem.GetForm().ToString() != "P(a, b)" {
			t.Fatalf("Form must be P(a, b)")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 03 -----")
	fmt.Println("----- EMPTY -----")
	tree2 := NewNode()
	tree2 = tree2.Insert(pa.(AST.Pred))
	var mix2 []subst.MixedSubstitutions
	_, mix2 = tree2.Unify(pb)
	if len(mix2) != 0 {
		t.Fatalf("can't Unify Predicat(Cst) and Predicat(Cst)")
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 04 -----")
	tree3 := NewNode()
	tree3 = tree3.Insert(pa.(AST.Pred))
	var mix3 []subst.MixedSubstitutions
	_, mix3 = tree3.Unify(pa)
	for _, elem := range mix3 {
		fmt.Println(elem.ToString())
	}
	if len(mix3) != 1 {
		t.Fatalf("Should return empty list")
	}
	for _, elem := range mix3 {
		if elem.GetForm().ToString() != "P(a)" {
			t.Fatalf("Must be P(a)")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 05 -----")
	tree4 := NewNode()
	tree4 = tree4.Insert(pax.(AST.Pred))
	var mix4 []subst.MixedSubstitutions
	_, mix4 = tree4.Unify(pafy)
	for _, elem := range mix4 {
		fmt.Println(elem.ToString())
	}
	if len(mix4) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix4 {
		if elem.GetForm().ToString() != "P(a, f(Y))" {
			t.Fatalf("Return must be P(a, f(Y))")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 06 -----")
	tree5 := NewNode()
	tree5 = tree5.Insert(pafx.(AST.Pred))
	var mix5 []subst.MixedSubstitutions
	_, mix5 = tree5.Unify(pafy)
	for _, elem5 := range mix5 {
		fmt.Println(elem5.ToString())
	}
	if len(mix5) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix5 {
		if elem.GetForm().ToString() != "P(a, f(Y))" {
			t.Fatalf("Must return P(a, f(Y))")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 07 -----")
	tree6 := NewNode()
	tree6 = tree6.Insert(px.(AST.Pred))
	var mix6 []subst.MixedSubstitutions
	_, mix6 = tree6.Unify(py)
	for _, elem := range mix6 {
		fmt.Println(elem.ToString())
	}
	if len(mix6) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix6 {
		fmt.Println(elem.GetForm().ToString())
		if elem.GetForm().ToString() != "P(Y)" {
			t.Fatalf("Must return P(Y)")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 08 -----")
	tree7 := NewNode()
	tree7 = tree7.Insert(pxy.(AST.Pred))
	var mix7 []subst.MixedSubstitutions
	_, mix7 = tree7.Unify(pab)
	for _, elem := range mix7 {
		fmt.Println(elem.ToString())
	}
	if len(mix7) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	for _, elem := range mix7 {
		if elem.GetForm().ToString() != "P(a, b)" {
			t.Fatalf("Must return P(a, b)")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 09 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree8 := NewNode()
	tree8 = tree8.Insert(pxx.(AST.Pred))
	val8, mix8 := tree8.Unify(pab)
	fmt.Println("-----EXPECTED FAILURE -----")

	if len(mix8) != 0 {
		fmt.Println("return must Be empty ")
	}
	if val8 {
		t.Fatalf("This test must fail")
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 10 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree9 := NewNode()
	tree9 = tree9.Insert(pba.(AST.Pred))
	tree9 = tree9.Insert(pab.(AST.Pred))
	val9, mix9 := tree9.Unify(pxx)
	if val9 {
		t.Fatalf(" This test must fail ")
	}
	if len(mix9) != 0 {
		t.Fatal("Return must be empty")
	}
	fmt.Println("-----EXPECTED FAILURE -----")
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 11 -----")
	tree10 := NewNode()
	tree10 = tree10.Insert(pb.(AST.Pred))
	tree10 = tree10.Insert(pa.(AST.Pred))
	tree10 = tree10.Insert(pfx.(AST.Pred))
	var mix10 []subst.MixedSubstitutions
	_, mix10 = tree10.Unify(py)

	if len(mix10) != 3 {
		t.Fatalf("Size must be 3")
	}
	for _, elem := range mix10 {
		if elem.GetForm().ToString() != "P(Y)" {
			t.Fatalf("Return must be P(Y)")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 12 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree11 := NewNode()
	tree11 = tree11.Insert(pab.(AST.Pred))
	val11, mix11 := tree11.Unify(pxx)
	if val11 {
		t.Fatalf("This test must fail ")
	}
	if len(mix11) != 0 {
		t.Fatalf("Size of mix11 must be empty")
	}

	fmt.Println("-----EXPECTED FAILURE -----")
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 13 -----")
	tree12 := NewNode()
	tree12 = tree12.Insert(pggab.(AST.Pred))
	var mix12 []subst.MixedSubstitutions
	_, mix12 = tree12.Unify(pxy)
	for _, elem := range mix12 {
		if elem.GetForm().ToString() != "P(X, Y)" {
			t.Fatalf("Return must be P(X, Y)")
		}
	}
	if len(mix12) != 1 {
		t.Fatalf("Should have a found 1 unification")
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

}

func TestUnifyTerm(t *testing.T) {

	fmt.Println("-----TEST 01 -----")
	tree := NewNode()
	tree = tree.Insert(pax.(AST.Pred))
	queryTerm := subst.TransformPred(pay.(AST.Pred))

	var val bool
	var mix []subst.MixedTermSubstitutions
	val, mix = tree.UnifyTerm(queryTerm)

	if val {
		for _, elem := range mix {
			fmt.Println("  ->", elem.ToString())
		}
	} else {
		t.Fatalf("Unify Failure")
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 02 -----")
	tree2 := NewNode()
	tree2 = tree2.Insert(pax.(AST.Pred))
	queryTerm2 := subst.TransformPred(pab.(AST.Pred))

	var mix2 []subst.MixedTermSubstitutions
	_, mix2 = tree2.UnifyTerm(queryTerm2)

	if len(mix2) != 1 {
		t.Fatalf("Unify Failure")
	}
	for _, elem := range mix2 {
		fmt.Println(elem.ToString())
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 03 -----")
	tree3 := NewNode()
	tree3 = tree3.Insert(pa.(AST.Pred))
	queryTerm3 := subst.TransformPred(pb.(AST.Pred))

	var val3 bool
	var mix3 []subst.MixedTermSubstitutions
	val3, mix3 = tree3.UnifyTerm(queryTerm3)

	if len(mix3) != 0 {
		t.Fatalf("Must return null because it can't be unified")
	}
	if val3 {
		t.Fatalf("Unify Failure")
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 04 -----")
	tree4 := NewNode()
	tree4 = tree4.Insert(pa.(AST.Pred))
	queryTerm4 := subst.TransformPred(pa.(AST.Pred))

	var val4 bool
	var mix4 []subst.MixedTermSubstitutions
	val4, mix4 = tree4.UnifyTerm(queryTerm4)

	if !val4 {
		t.Fatalf("Unify Failure")
	}
	for _, elem := range mix4 {
		if elem.ToString() != "P(a) {}" {
			t.Fatalf("Must be P(a) {}")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 05 -----")
	tree5 := NewNode()
	tree5 = tree5.Insert(pab.(AST.Pred))
	queryTerm5 := subst.TransformPred(pay.(AST.Pred))

	var mix5 []subst.MixedTermSubstitutions
	_, mix5 = tree5.UnifyTerm(queryTerm5)

	for _, elem := range mix5 {
		if elem.Term().ToString() != "P(a, Y)" {
			t.Fatalf("Return must be P(a, Y) ")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 06 -----")
	tree6 := NewNode()
	tree6 = tree6.Insert(pafx.(AST.Pred))
	queryTerm6 := subst.TransformPred(pafy.(AST.Pred))

	var mix6 []subst.MixedTermSubstitutions
	_, mix6 = tree6.UnifyTerm(queryTerm6)

	for _, elem := range mix6 {
		if elem.Term().ToString() != "P(a, f(Y))" {
			t.Fatalf("Must return P(a, f(Y))")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 07 -----")
	tree7 := NewNode()
	tree7 = tree7.Insert(px.(AST.Pred))
	queryTerm7 := subst.TransformPred(py.(AST.Pred))

	var mix7 []subst.MixedTermSubstitutions
	_, mix7 = tree7.UnifyTerm(queryTerm7)

	for _, elem := range mix7 {
		if elem.Term().ToString() != "P(Y)" {
			t.Fatalf("Must return P(Y)")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 08 -----")
	tree8 := NewNode()
	tree8 = tree8.Insert(pxy.(AST.Pred))
	queryTerm8 := subst.TransformPred(pab.(AST.Pred))

	var mix8 []subst.MixedTermSubstitutions
	_, mix8 = tree8.UnifyTerm(queryTerm8)

	for _, elem := range mix8 {
		if elem.Term().ToString() != "P(a, b)" {
			t.Fatalf("Must return P(a, b)")
		}
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 09 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree9 := NewNode()
	tree9 = tree9.Insert(pxx.(AST.Pred))
	queryTerm9 := subst.TransformPred(pab.(AST.Pred))

	var val9 bool
	val9, _ = tree9.UnifyTerm(queryTerm9)

	if val9 {
		t.Fatalf("Unify Failure")
	}
	fmt.Println("-----EXPECTED FAILURE -----")

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 10 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree10 := NewNode()
	tree10 = tree10.Insert(pba.(AST.Pred))
	tree10 = tree10.Insert(pab.(AST.Pred))
	queryTerm10 := subst.TransformPred(pxx.(AST.Pred))

	var val10 bool
	var mix10 []subst.MixedTermSubstitutions
	val10, mix10 = tree10.UnifyTerm(queryTerm10)

	if val10 {
		t.Fatalf("Got %d elements instead of 0", len(mix10))
	} else {
		fmt.Println("Unify Failure (Expected)")
	}
	fmt.Println("-----EXPECTED FAILURE -----")

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 11 -----")
	tree11 := NewNode()
	tree11 = tree11.Insert(pb.(AST.Pred))
	tree11 = tree11.Insert(pa.(AST.Pred))
	tree11 = tree11.Insert(pfx.(AST.Pred))
	queryTerm11 := subst.TransformPred(py.(AST.Pred))

	var mix11 []subst.MixedTermSubstitutions
	_, mix11 = tree11.UnifyTerm(queryTerm11)

	for _, elem := range mix11 {
		if elem.Term().ToString() != "P(Y)" {
			t.Fatalf("Unify Failure")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 12 -----")
	fmt.Println("-----EXPECTED FAILURE -----")

	tree12 := NewNode()
	tree12 = tree12.Insert(pab.(AST.Pred))
	queryTerm12 := subst.TransformPred(pxx.(AST.Pred))

	var val12 bool
	var mix12 []subst.MixedTermSubstitutions
	val12, mix12 = tree12.UnifyTerm(queryTerm12)

	if val12 {
		t.Fatalf("Got %d elements instead of 0", len(mix12))
	} else {
		fmt.Println("Unify Failure (Expected)")
	}
	if len(mix12) != 0 {
		t.Fatalf("Got %d elements instead of 0", len(mix12))

	}
	fmt.Println("-----EXPECTED FAILURE -----")
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 13 -----")
	tree13 := NewNode()
	tree13 = tree13.Insert(pggab.(AST.Pred))
	queryTerm13 := subst.TransformPred(pxy.(AST.Pred))

	var mix13 []subst.MixedTermSubstitutions
	_, mix13 = tree13.UnifyTerm(queryTerm13)

	for _, elem := range mix13 {
		if elem.Term().ToString() != "P(X, Y)" {
			t.Fatalf("Must return P(X, Y)")
		}
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

}

func TestMakeDataStruct(t *testing.T) {

	pac_form := not_pac.(AST.Not).GetForm().(AST.Pred)

	fmt.Println("Test positive tree")

	tree1 := NewNode()
	formulas1 := Lib.NewList[AST.Form]()
	formulas1.Append(pab)     // + => Insert
	formulas1.Append(not_pac) // - => Ignore
	formulas1.Append(pba)     // + => Insert

	resultTree1 := tree1.MakeDataStruct(formulas1, true).(DiscriminationNode)

	// Vérifications
	if len(resultTree1.RetrieveUnifiables(pab)) == 0 {
		t.Fatalf(" Tree must contain pab")
	}
	if len(resultTree1.RetrieveUnifiables(pba)) == 0 {
		t.Fatalf(" Tree must contain pba ")
	}
	if len(resultTree1.RetrieveUnifiables(pac_form)) != 0 {
		t.Fatalf(" Tree mustn't contain pac because it's negative in the positive tree")
	}

	fmt.Println("Test negative tree")

	tree2 := NewNode()
	formulas2 := Lib.NewList[AST.Form]()
	formulas2.Append(pab)     // + => Ignored
	formulas2.Append(not_pac) // - => Insert
	formulas2.Append(pba)     // + => Ignored

	resultTree2 := tree2.MakeDataStruct(formulas2, false).(DiscriminationNode)

	// Vérifications
	if len(resultTree2.RetrieveUnifiables(pac_form)) == 0 {
		t.Fatalf(" Tree must contain not_pac ")
	}
	if len(resultTree2.RetrieveUnifiables(pab)) != 0 {
		t.Fatalf(" Tree musn't contain pab because it's positive in the negative tree")
	}
	if len(resultTree2.RetrieveUnifiables(pba)) != 0 {
		t.Fatalf(" Tree mustn't contain pba because it's positive in the negative tree")
	}

	resultTree1.Print()
	resultTree2.Print()

}

func TestMaVieEllePueSaMere(t *testing.T) {

	metaIdentication(pax)

	metaIdentication(pabc)

}
