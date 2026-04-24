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
var pac AST.Form
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
var pfx AST.Form
var pafx AST.Form
var pafy AST.Form

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
	fx = AST.MakerFun(f_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.MkListV(y.GetTy()), Lib.MkListV[AST.Term](y))
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
	pac = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, c)))
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
	pfx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fx))
	pafy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fy))
	pafx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fx))
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d)))
	pa = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	pb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	PRa = AST.MakerPred(PR_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	PRb = AST.MakerPred(PR_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
}

/*
func initCodeTreesTests(lf Lib.List[AST.Form]) (Unif.DataStructure, Unif.DataStructure) {
	tp = Unif.NewNode()
	tn = Unif.NewNode()
	tp = tp.MakeDataStruct(lf, true)
	tn = tn.MakeDataStruct(lf, false)
	return tp, tn
}
*/

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

func TestFirstElementToSymbol(t *testing.T) {

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

func TestParser(t *testing.T) {

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
	tree = tree.Insert(pax.(AST.Pred)) // Cast
	tree = tree.Insert(pay.(AST.Pred))
	tree.Print()
	results := tree.RetrieveUnifiables(pab)
	if results.Len() == 0 {
		fmt.Println("C'est la merde")
	} else {
		fmt.Printf("Match : %d \n", results.Len())
	}
	for _, pred := range results.GetSlice() {
		fmt.Println(pred.ToString())
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
	tree = tree.Insert(pggab.(AST.Pred))

	nodeP := tree.getChildren().GetSlice()[0]
	remainingQuery := parseTerm(b).GetSlice()
	results := Lib.NewList[AST.Pred]()

	for _, child := range nodeP.getChildren().GetSlice() {
		matches := child.SkipTreeTermAndContinue(child.GetArity(), remainingQuery)
		results.Append(matches.GetSlice()...)
	}

	if results.Len() != 2 {
		t.Fatalf("error")
	}

	for _, res := range results.GetSlice() {
		fmt.Println("=>", res.ToString())
	}
}

func TestRetrieveUnifiables(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pax.(AST.Pred))
	tree = tree.Insert(pba.(AST.Pred))
	res := tree.RetrieveUnifiables(pay)

	if res.Len() != 1 {
		t.Fatalf("Should be only 1")
	}

	for _, pred := range res.GetSlice() {

		fmt.Println(len(res.GetSlice())) // Doublon
		fmt.Println("=>", pred.ToString())
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
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 09 -----")
	tree8 := NewNode()
	tree8 = tree8.Insert(pxx.(AST.Pred))
	var mix8 []subst.MixedSubstitutions
	_, mix8 = tree8.Unify(pab)
	if len(mix8) != 0 {
		t.Fatalf("Got %d elements instead of 0", len(mix8))
	}

	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 10 -----")
	tree9 := NewNode()
	tree9 = tree9.Insert(pba.(AST.Pred))
	tree9 = tree9.Insert(pab.(AST.Pred))
	var mix9 []subst.MixedSubstitutions
	_, mix9 = tree9.Unify(pxx)
	if len(mix9) != 0 {
		t.Fatalf("Got %d elements instead of 0", len(mix9))
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 11 -----")
	tree10 := NewNode()
	tree10 = tree10.Insert(pb.(AST.Pred))
	tree10 = tree10.Insert(pa.(AST.Pred))
	tree10 = tree10.Insert(pfx.(AST.Pred))
	var mix10 []subst.MixedSubstitutions
	_, mix10 = tree10.Unify(py)
	for _, elem := range mix10 {
		fmt.Println(elem.ToString())
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 12 -----")
	tree11 := NewNode()
	tree11 = tree11.Insert(pab.(AST.Pred))
	var mix11 []subst.MixedSubstitutions
	_, mix11 = tree11.Unify(pxx)
	if len(mix11) != 0 {
		t.Fatalf("Got %d elements instead of 0", len(mix11))
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

	fmt.Println("-----TEST 13 -----")
	tree12 := NewNode()
	tree12 = tree12.Insert(pggab.(AST.Pred))
	var mix12 []subst.MixedSubstitutions
	_, mix12 = tree12.Unify(pxy)
	for _, elem := range mix12 {
		fmt.Println(elem.ToString())
	}
	fmt.Println("-----END TEST-----")
	fmt.Println()

}

func TestMakeDataStruct(t *testing.T) {
	tree := NewNode()
	formulas := Lib.NewList[AST.Form]()
	formulas.Append(pxy)
	tree2 := tree.MakeDataStruct(formulas, true)
	tree2.Print()

	tree3 := NewNode()
	formulas2 := Lib.NewList[AST.Form]()
	formulas2.Append(pab)
	formulas2.Append(pac)
	formulas2.Append(pba)
	tree4 := tree3.MakeDataStruct(formulas2, true)
	tree4.Print()

	tree5 := NewNode()
	formulas3 := Lib.NewList[AST.Form]()
	formulas3.Append(pac)
	tree6 := tree5.MakeDataStruct(formulas3, true)
	tree6.Print()

}
