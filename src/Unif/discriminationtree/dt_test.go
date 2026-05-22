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
	"os"
	"testing"
	"time"

	"github.com/GoelandProver/Goeland/AST"
	"github.com/GoelandProver/Goeland/Glob"
	"github.com/GoelandProver/Goeland/Lib"
	"github.com/GoelandProver/Goeland/Typing"
	subst "github.com/GoelandProver/Goeland/Unif/substitution"
)

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
var P2_id AST.Id

// Meta
var x AST.Meta
var v1 AST.Meta
var v2 AST.Meta
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

var gax AST.Fun
var gxb AST.Fun
var gyb AST.Fun
var gab AST.Fun
var gxc AST.Fun
var ggx AST.Fun
var gga AST.Fun
var gfy AST.Fun
var gfa AST.Fun
var gahc AST.Fun
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
var f_x_x AST.Fun
var f_y_y AST.Fun
var f_z_z AST.Fun
var f_gax_c AST.Fun
var f_gxb_y AST.Fun
var f_gyb_z AST.Fun
var f_gab_a AST.Fun
var f_gxc_b AST.Fun
var f_z_y AST.Fun
var f_x_y AST.Fun

// Form
var pggab AST.Form
var not_pac AST.Form
var not_pba AST.Form
var pa AST.Form
var pb AST.Form

var not_pc AST.Form
var pab AST.Form
var paa AST.Form
var pbb AST.Form

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
var pfy AST.Form
var pafx AST.Form
var pafy AST.Form
var pfac AST.Form

var pfgaxc AST.Form
var pfgxby AST.Form
var pfgybz AST.Form
var pfgaba AST.Form
var pfgxcb AST.Form
var pfzy AST.Form
var pfxy AST.Form
var pfxx AST.Form
var pfzz AST.Form

var not_pcd AST.Form

var P2a AST.Form
var P2b AST.Form

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
	P2_id = AST.MakerId("P2")

	// Meta
	x = AST.MakerMeta("X", -1, AST.TIndividual())
	v1 = AST.MakeMeta(1, 0, "v1", 0, AST.TIndividual())
	v2 = AST.MakeMeta(2, 0, "v2", 0, AST.TIndividual())
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
	gax = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, x))
	gxb = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, b))
	gyb = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, b))
	gab = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	gxc = AST.MakerFun(g_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, c))
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
	f_x_x = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, x))
	f_y_y = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](y, y))
	f_z_z = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z, z))
	f_gax_c = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gax, c))
	f_gxb_y = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gxb, y))
	f_gyb_z = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gyb, z))
	f_gab_a = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gab, a))
	f_gxc_b = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gxc, b))
	f_z_y = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](z, y))
	f_x_y = AST.MakerFun(f_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](x, y))

	// Predicates
	pggab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](gga, b))
	not_pac = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, c)))
	not_pba = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, a)))
	not_pc = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c)))
	pab = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, b))
	paa = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, a))
	pbb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b, b))
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
	pfy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fy))
	pafy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fy))
	pafx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a, fx))
	pfac = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](fa, c))
	pfgaxc = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_gax_c))
	pfgxby = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_gxb_y))
	pfgybz = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_gyb_z))
	pfgaba = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_gab_a))
	pfgxcb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_gxc_b))
	pfzy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_z_y))
	pfxy = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_x_y))
	pfxx = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_x_x))
	pfzz = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](f_z_z))
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](c, d)))
	pa = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	pb = AST.MakerPred(p_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
	P2a = AST.MakerPred(P2_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](a))
	P2b = AST.MakerPred(P2_id, Lib.NewList[AST.Ty](), Lib.MkListV[AST.Term](b))
}

// Typed Part

var p_typed_id AST.Id
var b_typed_id AST.Id
var a_typed_id AST.Id
var a_typed AST.Ty
var p_typed_pred_Const_A AST.Pred
var p_typed_pred_Const_B AST.Pred
var p_typed_pred_int_2 AST.Pred
var p_typed_pred_int_3 AST.Pred
var p_typed_pred_int_int AST.Pred
var p_typed_pred_int_x AST.Pred
var p_typed_pred_reel_x AST.Pred
var p_typed_pred_rational_x AST.Pred

var p_id_typed AST.Id
var p_typed AST.Pred
var random_type AST.Ty
var banane_id AST.Id
var banane AST.Term
var meta_typee AST.Term

func initTestVariable2() {

	p_typed_id = AST.MakerId("p")
	b_typed_id = AST.MakerId("b")
	a_typed_id = AST.MakerId("A")

	A := AST.MkTyConst("A")
	B := AST.MkTyConst("B")

	x = AST.MakerMeta("X", -1, AST.TIndividual())

	p_typed_pred_Const_A = AST.MakerPred(p_typed_id,
		Lib.MkListV(A),
		Lib.MkListV[AST.Term](AST.MakerConst(a_typed_id)),
	)

	p_typed_pred_Const_B = AST.MakerPred(p_typed_id,
		Lib.MkListV(B),
		Lib.MkListV[AST.Term](AST.MakerConst(b_typed_id)),
	)

	p_typed_pred_int_x = AST.MakerPred(p_typed_id,
		Lib.MkListV(AST.TInt()),
		Lib.MkListV[AST.Term](x),
	)

	p_typed_pred_reel_x = AST.MakerPred(p_typed_id,
		Lib.MkListV(AST.TReal()),
		Lib.MkListV[AST.Term](x),
	)

	p_typed_pred_rational_x = AST.MakerPred(p_typed_id,
		Lib.MkListV(AST.TRat()),
		Lib.MkListV[AST.Term](x),
	)

	p_typed_pred_int_3 = AST.MakerPred(p_typed_id,
		Lib.MkListV(AST.MkTyConst("int")),
		Lib.MkListV[AST.Term](AST.MakerConst(AST.MakerId("3"))),
	)

	p_typed_pred_int_2 = AST.MakerPred(p_typed_id,
		Lib.MkListV(AST.TInt()),
		Lib.MkListV[AST.Term](AST.MakerConst(AST.MakerId("2"))),
	)

	random_type = AST.MakerTyBV("random_type")
	p_id_typed = AST.MakerId("p_typed")
	meta_typee = AST.MakerMeta("Z", -1, random_type)
	p_typed = AST.MakerPred(p_id_typed, Lib.MkListV(random_type), Lib.MkListV(meta_typee))
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
	initTestVariable2()
	Glob.EnableDebug()
	code := m.Run()
	os.Exit(code)
}

func TestFirstElementToSymbolType(t *testing.T) {

	t.Run("Fun_Multiple_Args", func(t *testing.T) {
		st := FirstElementToSymbolType(fxy)
		if st.GetArity() != 2 {
			t.Errorf("Expected arity 2 for f(x, y), got %d", st.GetArity())
		}
	})

	t.Run("Fun_Constant", func(t *testing.T) {
		st := FirstElementToSymbolType(a)
		if st.GetArity() != 0 {
			t.Errorf("Expected arity 0 for constant a, got %d", st.GetArity())
		}
	})

	t.Run("Meta_Variable", func(t *testing.T) {
		st := FirstElementToSymbolType(x)
		if st.GetArity() != 0 {
			t.Errorf("Expected arity 0 for Meta variable x, got %d", st.GetArity())
		}
		if !st.getSymbol().IsMeta() {
			t.Errorf("Expected symbol to be recognized as Meta")
		}
	})

	t.Run("Id_Type", func(t *testing.T) {
		st := FirstElementToSymbolType(f_id)
		if st.GetArity() != 0 {
			t.Errorf("Expected arity 0 for ID type, got %d", st.GetArity())
		}
	})

	t.Run("Complex_Fun", func(t *testing.T) {
		// f_gax_c represents f(g(a, x), c), which has 2 direct top-level arguments
		st := FirstElementToSymbolType(f_gax_c)
		if st.GetArity() != 2 {
			t.Errorf("Expected arity 2 for complex function f_gax_c, got %d", st.GetArity())
		}
	})

	t.Run("Exception_On_Nil_Term", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Expected a panic/exception when passing nil to FirstElementToSymbolType, but it completed without panicking")
			}
		}()
		// Passing nil will trigger the default case inside the switch block or cause a controlled crash
		FirstElementToSymbolType(nil)
	})
}
func TestTermToNode(t *testing.T) {

	t.Run("Nominal_Fun_Single_Arg", func(t *testing.T) {

		node := TermToNode(ggx)
		if node.GetArity() != 1 {
			t.Errorf("Expected arity 1 for ggx, got %d", node.GetArity())
		}
		if node.getChildren().Len() != 1 {
			t.Errorf("Expected 1 child node for ggx, got %d", node.getChildren().Len())
		}
	})

	t.Run("Nominal_Fun_Multiple_Args", func(t *testing.T) {

		node := TermToNode(fbc)
		if node.GetArity() != 2 {
			t.Errorf("Expected arity 2 for fbc, got %d", node.GetArity())
		}
		if node.getChildren().Len() != 2 {
			t.Errorf("Expected 2 child nodes for fbc, got %d", node.getChildren().Len())
		}
	})

	t.Run("Nominal_Constant", func(t *testing.T) {

		node := TermToNode(a)
		if node.GetArity() != 0 {
			t.Errorf("Expected arity 0 for constant 'a', got %d", node.GetArity())
		}
		if node.getChildren().Len() != 0 {
			t.Errorf("Expected 0 child nodes for constant 'a', got %d", node.getChildren().Len())
		}
	})

	t.Run("Nominal_Meta", func(t *testing.T) {

		node := TermToNode(x)
		if node.GetArity() != 0 {
			t.Errorf("Expected arity 0 for Meta variable 'x', got %d", node.GetArity())
		}
		if node.getChildren().Len() != 0 {
			t.Errorf("Expected 0 child nodes for Meta variable, got %d", node.getChildren().Len())
		}
	})

	t.Run("Nominal_Id", func(t *testing.T) {

		node := TermToNode(f_id)
		if node.GetArity() != 0 {
			t.Errorf("Expected arity 0 for ID type 'f_id', got %d", node.GetArity())
		}
	})

	t.Run("Exception_On_Nil_Term", func(t *testing.T) {

		defer func() {
			if r := recover(); r == nil {
				t.Error("Expected a panic/exception when passing nil to TermToNode, but it completed without panicking")
			}
		}()
		TermToNode(nil)
	})
}

func TestCreateNodeElement(t *testing.T) {
	// --- NOMINAL TESTS ---

	// 1. Testing the "string" case
	t.Run("Nominal_String", func(t *testing.T) {
		strInput := "test_identifier"
		node := createNodeElement(strInput)

		// Verify it returns a NodeString
		if ns, ok := node.(NodeString); !ok {
			t.Errorf("Expected return type NodeString, got %T", node)
		} else if ns.ToString() != strInput {
			t.Errorf("Expected NodeString value to be '%s', got '%s'", strInput, ns.ToString())
		}
	})

	// 2. Testing the "AST.Ty" case
	t.Run("Nominal_AST_Ty", func(t *testing.T) {
		// random_type is defined in dt_test.go (e.g., AST.MakerTyBV("random_type"))
		node := createNodeElement(random_type)

		// Verify it returns a TyNode
		if _, ok := node.(TyNode); !ok {
			t.Errorf("Expected return type TyNode for AST.Ty input, got %T", node)
		}
	})

	// 3. Testing the "AST.Pred" case
	t.Run("Nominal_AST_Pred", func(t *testing.T) {
		// 'pa' is a predicate P(a) defined in dt_test.go
		node := createNodeElement(pa.(AST.Pred))

		// Verify it returns a TermNode (because predicates are transformed into terms)
		termNode, ok := node.(TermNode)
		if !ok {
			t.Errorf("Expected return type TermNode for AST.Pred input, got %T", node)
		}

		// Verify the underlying transformation occurred (P(a) should now be treated as a Fun)
		if !termNode.Term.IsFun() {
			t.Errorf("Expected the transformed AST.Pred to be wrapped as an AST.Fun inside the TermNode")
		}
	})

	// 4. Testing the "AST.Term" case
	t.Run("Nominal_AST_Term", func(t *testing.T) {
		// 'fxy' is an AST.Fun (which implements AST.Term) defined in dt_test.go
		node := createNodeElement(fxy)

		// Verify it returns a TermNode directly without issues
		if _, ok := node.(TermNode); !ok {
			t.Errorf("Expected return type TermNode for AST.Term input, got %T", node)
		}
	})

	// --- FAILING TESTS (EXPECTING EXCEPTIONS) ---

	// 5. Testing an unhandled data type (e.g., an integer)
	t.Run("Exception_On_Unhandled_Type", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Expected a panic/exception when passing an integer, but it completed without panicking")
			}
		}()

		// Passing an int will trigger the 'default' case and cause Glob.Anomaly to panic
		createNodeElement(42)
	})

	// 6. Testing a nil input
	t.Run("Exception_On_Nil", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Expected a panic/exception when passing nil, but it completed without panicking")
			}
		}()

		// Passing nil will trigger the 'default' case
		createNodeElement(nil)
	})
}

func TestInsert(t *testing.T) {

	t.Run("Nominal_Multiple_Inserts", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pba.(AST.Pred))
		tree = tree.Insert(pab.(AST.Pred))
		tree = tree.Insert(pafx.(AST.Pred))
		tree = tree.Insert(pafy.(AST.Pred))

		children := tree.getChildren().GetSlice()
		if len(children) != 1 {
			t.Errorf("Expected root node to have exactly 1 child (the 'P' predicate node), got %d", len(children))
		}
		pNode := children[0]
		if pNode.GetArity() != 2 {
			t.Errorf("Expected the 'P' node to have arity 2, got %d", pNode.GetArity())
		}
	})

	t.Run("Nominal_Single_Nested_Insert", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pfx.(AST.Pred))
		children := tree.getChildren().GetSlice()
		if len(children) != 1 {
			t.Fatalf("Expected root node to have exactly 1 child, got %d", len(children))
		}
		pNode := children[0]
		if pNode.GetArity() != 1 {
			t.Errorf("Expected the 'P' node to have arity 1, got %d", pNode.GetArity())
		}
	})

	t.Run("Nominal_Insert_Variable_Overlap", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pfx.(AST.Pred))
		tree = tree.Insert(pfy.(AST.Pred))

		children := tree.getChildren().GetSlice()
		if len(children) != 1 {
			t.Fatalf("Expected root node to have exactly 1 child, got %d", len(children))
		}

	})

	t.Run("Exception_Arity_Collision", func(t *testing.T) {
		defer func() {
			if r := recover(); r == nil {
				t.Error("Expected a panic when inserting a predicate with a conflicting arity on an existing path")
			}
		}()

		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		tree = tree.Insert(pabc.(AST.Pred)) // Arity Error
		tree.Print()
	})
}

func TestPrintDoublonCheck(t *testing.T) {

	tree := NewNode()
	tree = tree.Insert(pa.(AST.Pred))
	tree = tree.Insert(pa.(AST.Pred))
	tree.Print()

	if tree.getChildren().Len() != 1 {
		t.Fatalf("Error Duplicate Branch")
	}

}

func TestPrintHugeTree(t *testing.T) {

	t.Run("Nominal_Huge_Tree_Structure", func(t *testing.T) {
		tree := NewNode()

		tree = tree.Insert(pfgaxc.(AST.Pred))
		tree = tree.Insert(pfgxby.(AST.Pred))
		tree = tree.Insert(pfgybz.(AST.Pred))
		tree = tree.Insert(pfgaba.(AST.Pred))
		tree = tree.Insert(pfgxcb.(AST.Pred))
		tree = tree.Insert(pfzy.(AST.Pred))
		tree = tree.Insert(pfxy.(AST.Pred))
		tree = tree.Insert(pfxx.(AST.Pred))
		tree = tree.Insert(pfzz.(AST.Pred))
		tree.Print()

		rootChildren := tree.getChildren().GetSlice()
		if len(rootChildren) != 1 { // P
			t.Fatalf("Expected the root node to have exactly 1 child (the 'P' predicate), got %d", len(rootChildren))
		}

		pNode := rootChildren[0]
		if pNode.GetArity() != 1 { // P
			t.Errorf("Expected 'P' node to have arity 1, got %d", pNode.GetArity())
		}

		pChildren := pNode.getChildren().GetSlice()
		if len(pChildren) != 1 { // f()
			t.Fatalf("Expected 'P' node to have exactly 1 child (the 'f' function), got %d", len(pChildren))
		}

		fNode := pChildren[0]
		if fNode.GetArity() != 2 { // g() & v1
			t.Errorf("Expected 'f' node to have arity 2, got %d", fNode.GetArity())
		}

		fChildren := fNode.getChildren().GetSlice()
		if len(fChildren) != 2 { // g() & v1
			t.Fatalf("Expected 'f' node to branch into exactly 2 paths ('g' and a Meta variable), got %d", len(fChildren))
		}

		// Determine who is g and who is v1
		var gNode, metaNode *DiscriminationNode
		for i := range fChildren {
			if fChildren[i].getSymbol().getSymbol().IsMeta() {
				metaNode = &fChildren[i]
			} else {
				gNode = &fChildren[i]
			}
		}

		if gNode == nil || metaNode == nil {
			t.Fatalf("Expected to find one 'g' node and one Meta node as children of 'f'")
		}

		if metaNode.GetArity() != 0 {
			t.Errorf("Expected Meta node to have arity 0, got %d", metaNode.GetArity())
		}

		if metaNode.getChildren().Len() != 2 {
			t.Fatalf("v1 must have 2 children, v1 and v2")
		}

		meta1Meta2Node := metaNode.getChildren().At(0)
		meta1Meta1Node := metaNode.getChildren().At(1)

		if meta1Meta2Node.getChildren().Len() != 0 {
			t.Fatalf("Must have 0 children")
		}
		if meta1Meta2Node.getLeafFor().Len() != 2 {
			t.Fatalf("Must have 2 Leaf")
		}

		if meta1Meta1Node.getChildren().Len() != 0 {
			t.Fatalf("Must have 0 children")
		}
		if meta1Meta1Node.getLeafFor().Len() != 2 {
			t.Fatalf("Must have 2 Leaf")
		}

		if gNode.GetArity() != 2 { // g(arg1, arg2)
			t.Errorf("Expected 'g' node to have arity 2, got %d", gNode.GetArity())
		}

		gChildren := gNode.getChildren().GetSlice()
		if len(gChildren) != 2 {
			t.Fatalf("Expected 'g' node to branch into exactly 2 paths ('a' and a Meta variable), got %d", len(gChildren))
		}

		aNode := gChildren[0]
		gMetaNode := gChildren[1]

		if aNode.getSymbol().getSymbol().ToString() != "a" {
			t.Errorf("Expected first child of 'g' to be 'a', got %s", aNode.getSymbol().getSymbol().ToString())
		}

		aChildren := aNode.getChildren().GetSlice()
		if len(aChildren) != 2 {
			t.Fatalf("Expected 'a' node to have exactly 2 children (Meta 'v1' and constant 'b'), got %d", len(aChildren))
		}

		aMetaNode := aChildren[0]
		abNode := aChildren[1]

		if !aMetaNode.getSymbol().getSymbol().IsMeta() {
			t.Errorf("Expected first child of 'a' to be a Meta variable")
		}
		if aMetaNode.getChildren().Len() != 1 {
			t.Fatalf("Expected 'v1' under 'a' to have 1 child ('c'), got %d", aMetaNode.getChildren().Len())
		}
		acNode := aMetaNode.getChildren().At(0)
		if acNode.getSymbol().getSymbol().ToString() != "c" {
			t.Errorf("Expected node to be 'c', got %s", acNode.getSymbol().getSymbol().ToString())
		}
		if acNode.getLeafFor().Len() != 1 {
			t.Errorf("Expected 'c' node to have exactly 1 leaf formula (pfgaxc), got %d", acNode.getLeafFor().Len())
		}

		if abNode.getSymbol().getSymbol().ToString() != "b" {
			t.Errorf("Expected second child of 'a' to be 'b', got %s", abNode.getSymbol().getSymbol().ToString())
		}
		if abNode.getChildren().Len() != 1 {
			t.Fatalf("Expected 'b' under 'a' to have 1 child ('a'), got %d", abNode.getChildren().Len())
		}
		abaNode := abNode.getChildren().At(0)
		if abaNode.getSymbol().getSymbol().ToString() != "a" {
			t.Errorf("Expected leaf node to be 'a', got %s", abaNode.getSymbol().getSymbol().ToString())
		}
		if abaNode.getLeafFor().Len() != 1 {
			t.Errorf("Expected leaf 'a' node to have exactly 1 leaf formula (pfgaba), got %d", abaNode.getLeafFor().Len())
		}

		if !gMetaNode.getSymbol().getSymbol().IsMeta() {
			t.Errorf("Expected second child of 'g' to be a Meta variable")
		}

		gMetaChildren := gMetaNode.getChildren().GetSlice()
		if len(gMetaChildren) != 2 {
			t.Fatalf("Expected 'v1' under 'g' to have 2 children ('b' and 'c'), got %d", len(gMetaChildren))
		}

		gbNode := gMetaChildren[0]
		gcNode := gMetaChildren[1]

		if gbNode.getSymbol().getSymbol().ToString() != "b" {
			t.Errorf("Expected first child of 'v1' under 'g' to be 'b', got %s", gbNode.getSymbol().getSymbol().ToString())
		}
		if gbNode.getChildren().Len() != 1 {
			t.Fatalf("Expected 'b' under 'v1' to have 1 child (Meta 'v2'), got %d", gbNode.getChildren().Len())
		}
		gbMetaNode := gbNode.getChildren().At(0)
		if !gbMetaNode.getSymbol().getSymbol().IsMeta() {
			t.Errorf("Expected child of 'b' to be a Meta variable 'v2'")
		}
		if gbMetaNode.getLeafFor().Len() != 2 {
			t.Errorf("Expected 'v2' node to contain exactly 2 leaf formulas (pfgxby and pfgybz), got %d", gbMetaNode.getLeafFor().Len())
		}

		if gcNode.getSymbol().getSymbol().ToString() != "c" {
			t.Errorf("Expected second child of 'v1' under 'g' to be 'c', got %s", gcNode.getSymbol().getSymbol().ToString())
		}
		if gcNode.getChildren().Len() != 1 {
			t.Fatalf("Expected 'c' under 'v1' to have 1 child ('b'), got %d", gcNode.getChildren().Len())
		}
		gcbNode := gcNode.getChildren().At(0)
		if gcbNode.getSymbol().getSymbol().ToString() != "b" {
			t.Errorf("Expected leaf node to be 'b', got %s", gcbNode.getSymbol().getSymbol().ToString())
		}
		if gcbNode.getLeafFor().Len() != 1 {
			t.Errorf("Expected leaf 'b' node to have exactly 1 leaf formula (pfgxcb), got %d", gcbNode.getLeafFor().Len())
		}
	})
}

func TestParseTerm(t *testing.T) {

	t.Run("Parse_Simple_fxy", func(t *testing.T) {
		tmpContext := NewContext()
		seqList := parseTerm(fxy, tmpContext)
		seq := seqList.GetSlice()

		if len(seq) != 3 {
			t.Fatalf("Expected 3 elements for f(x,y), got %d", len(seq))
		}

		if seq[0].GetArity() != 2 || seq[0].getSymbol().ToString() != "f" {
			t.Fatal("Element 0 must be function 'f' with arity 2")
		}

		if seq[1].GetArity() != 0 || !seq[1].getSymbol().IsMeta() {
			t.Fatal("Element 1 must be meta variable 'v1' with arity 0")
		}

		if seq[2].GetArity() != 0 || !seq[2].getSymbol().IsMeta() {
			t.Fatal("Element 2 must be meta variable 'v2' with arity 0")
		}
	})
	t.Run("Parse_Nested_Left_f_fxy_z", func(t *testing.T) {
		tmpContext2 := NewContext()
		seqList := parseTerm(f_fxy_z, tmpContext2)
		seq := seqList.GetSlice()

		if len(seq) != 5 {
			t.Fatalf("Expected 5 elements for f(f(x,y), z), got %d", len(seq))
		}

		if seq[0].GetArity() != 2 || seq[0].getSymbol().ToString() != "f" {
			t.Fatal("Element 0 must be the outer function 'f' with arity 2")
		}

		if seq[1].GetArity() != 2 || seq[1].getSymbol().ToString() != "f" {
			t.Fatal("Element 1 must be the inner function 'f' with arity 2")
		}

		if seq[2].GetArity() != 0 || !seq[2].getSymbol().IsMeta() {
			t.Fatal("Element 2 must be meta variable 'v1' with arity 0")
		}

		if seq[3].GetArity() != 0 || !seq[3].getSymbol().IsMeta() {
			t.Fatal("Element 3 must be meta variable 'v2' with arity 0")
		}

		if seq[4].GetArity() != 0 || !seq[4].getSymbol().IsMeta() {
			t.Fatal("Element 4 must be meta variable 'v3' with arity 0")
		}
	})

	t.Run("Parse_Nested_Right_f_x_fyz", func(t *testing.T) {
		tmpContext4 := NewContext()
		seqList := parseTerm(f_x_fyz, tmpContext4)
		seq := seqList.GetSlice()

		if len(seq) != 5 {
			t.Fatalf("Expected 5 elements for f(x, f(y,z)), got %d", len(seq))
		}

		if seq[0].GetArity() != 2 || seq[0].getSymbol().ToString() != "f" {
			t.Fatal("Element 0 must be outer function 'f' with arity 2")
		}

		if seq[1].GetArity() != 0 || !seq[1].getSymbol().IsMeta() {
			t.Fatal("Element 1 must be meta variable 'v1' with arity 0")
		}

		if seq[2].GetArity() != 2 || seq[2].getSymbol().ToString() != "f" {
			t.Fatal("Element 2 must be inner function 'f' with arity 2")
		}

		if seq[3].GetArity() != 0 || !seq[3].getSymbol().IsMeta() {
			t.Fatal("Element 3 must be meta variable 'v2' with arity 0")
		}

		if seq[4].GetArity() != 0 || !seq[4].getSymbol().IsMeta() {
			t.Fatal("Element 4 must be meta variable 'v3' with arity 0")
		}
	})
}

func TestRetrieve(t *testing.T) {

	t.Run("RetrieveUnifiable_pax_pay_and_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		tree = tree.Insert(pay.(AST.Pred))
		results := tree.RetrieveUnifiables(pab)
		if len(results) != 2 {
			t.Fatalf("Must return 2 element")
		} else {
			fmt.Printf("returned %d element", len(results))
		}

	})

	t.Run("RetrieveUnifiable_pax_pxy_and_pab", func(t *testing.T) {

		fmt.Println()
		tree2 := NewNode()
		tree2 = tree2.Insert(pxy.(AST.Pred))
		results2 := tree2.RetrieveUnifiables(pab)
		if len(results2) != 1 {
			t.Fatalf("Supposed to have 1 CandidatResults")
		}
		resultat3 := ToSingleElement(results2)
		if len(resultat3.GetSubs()) != 2 {
			t.Fatalf("Supposed to have 2 unifiables")
		}

	})

}
func TestEquals(t *testing.T) {

	t.Run("x Equals x", func(t *testing.T) {

		ok := x.Equals(x)
		if !ok {
			t.Fatalf("Equals Test failure on x Equals x ")
		}

	})

	t.Run("pxx Equals pxx", func(t *testing.T) {

		ok2 := pxx.Equals(pxx)
		if !ok2 {
			t.Fatalf("Equals Test failure on pxx Equals pxx ")
		}

	})

	t.Run("fab Equals fab", func(t *testing.T) {

		ok3 := fab.Equals(fab)
		if !ok3 {
			t.Fatalf("Equals Test failure on pab Equals pab ")
		}

	})

	t.Run("fab Equals fay", func(t *testing.T) {

		ok4 := fab.Equals(fay)
		if ok4 {
			t.Fatalf("Equals Test Succes on fab Equals fay")
		}

	})

	t.Run("fx Equals fy", func(t *testing.T) {

		ok5 := fx.Equals(fy)
		if ok5 {
			t.Fatalf("Equals Test Succes on fab Equals fay")
		}

	})

}

func TestGetSubTermLength(t *testing.T) {

	Context := NewContext()

	t.Run("SubTerm_ggx", func(t *testing.T) {

		seq := parseTerm(ggx, Context).GetSlice()
		var1 := (GetSubTermLength(seq))
		if var1 != 3 {
			t.Fatalf("Error SubTerLength with 2functions & 1Meta ")
		}
	})
	Context.Reset()

	t.Run("SubTerm_fxy", func(t *testing.T) {
		seq2 := parseTerm(fxy, Context).GetSlice()
		var2 := (GetSubTermLength(seq2))
		if var2 != 3 {
			t.Fatalf("Error SubTerLength with 1function & 2Meta")
		}
		Context.Reset()
	})

	t.Run("SubTerm_gx", func(t *testing.T) {

		seq3 := parseTerm(gx, Context).GetSlice()
		var3 := (GetSubTermLength(seq3))
		if var3 != 2 {
			t.Fatalf("Error SubTerLength with 1function & 1Meta")
		}
		Context.Reset()
	})

	t.Run("SubTerm_ga", func(t *testing.T) {

		seq4 := parseTerm(ga, Context).GetSlice()
		var4 := (GetSubTermLength(seq4))
		if var4 != 2 {
			t.Fatalf("Error SubTerLength with 1function & 1cst")
		}
		Context.Reset()
	})

	t.Run("SubTerm_gggx", func(t *testing.T) {

		seq5 := parseTerm(gggx, Context).GetSlice()
		var5 := (GetSubTermLength(seq5))
		if var5 != 4 {
			t.Fatalf("Error SubTerLength with 1function & 3Meta")
		}
		Context.Reset()
	})

	t.Run("SubTerm_f_y_y", func(t *testing.T) {

		seq6 := parseTerm(f_y_y, Context).GetSlice()
		var6 := (GetSubTermLength(seq6))
		if var6 != 3 {
			t.Fatalf("Error SubTerLength with 1function & 2Meta")
		}
	})

}

func TestSkipTreeTermAndContinue(t *testing.T) {

	t.Run("SkipTreeTermAndContinue_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		needed := 1
		emptyQuery := []SymbolType{}
		emptyEnv := subst.Substitutions{}
		results := tree.SkipTreeTermAndContinue(needed, emptyQuery, emptyEnv)
		if len(results) != 1 {
			t.Fatalf(" Expected 1 Element, got %d", len(results))
		}
	})

	t.Run("SkipTreeTermAndContinue_px", func(t *testing.T) {

		tree2 := NewNode()
		tree2 = tree2.Insert(px.(AST.Pred))
		needed2 := 1
		emptyQuery2 := []SymbolType{}
		emptyEnv2 := subst.Substitutions{}
		results2 := tree2.SkipTreeTermAndContinue(needed2, emptyQuery2, emptyEnv2)
		if len(results2) != 1 {
			t.Fatalf(" Expected 1 Element, got %d", len(results2))
		}
	})

	t.Run("SkipTreeTermAndContinue_pab_pba", func(t *testing.T) {

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
	})

	t.Run("SkipTreeTermAndContinue_pab_pab_pca", func(t *testing.T) {

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
	})

}

func TestRetrieveUnifiables(t *testing.T) {

	tree := NewNode()
	candidat := []CandidatResult{}

	t.Run("TestRetrieveUnifiables_pax_pba", func(t *testing.T) {

		tree = tree.Insert(pax.(AST.Pred))
		tree = tree.Insert(pba.(AST.Pred))
		candidat = tree.RetrieveUnifiables(pay)
		if len(candidat) != 1 {
			t.Fatalf("Should be only 1")
		}

	})

	t.Run("TestRetrieveUnifiables_pafx", func(t *testing.T) {

		tree = tree.Insert(pafx.(AST.Pred))
		candidat = tree.RetrieveUnifiables(pay)
		if len(candidat) != 2 {
			t.Fatalf("Should be only 2")
		}

	})

	t.Run("TestRetrieveUnifiables_pafy", func(t *testing.T) {

		tree = tree.Insert(pafy.(AST.Pred))
		candidat = tree.RetrieveUnifiables(pay)
		if len(candidat) != 3 {
			t.Fatalf("Should be only 3")
		}

	})

	t.Run("TestRetrieveUnifiables_pa", func(t *testing.T) {

		tree2 := NewNode()
		tree2 = tree2.Insert(pa.(AST.Pred))
		candidat2 := tree2.RetrieveUnifiables(pb)
		if len(candidat2) != 0 {
			t.Fatalf("Should be 0 because pa and pb can't be unified")
		}

	})

}

func TestCopy(t *testing.T) {

	t.Run("TestCopy_pax", func(t *testing.T) {

		tree1 := NewNode()
		tree2 := tree1.Copy()
		tree1 = tree1.Insert(pax.(AST.Pred))
		res2 := tree2.IsEmpty()
		if !res2 {
			t.Fatalf("Tree2 is not a copy, it s only a pointer to tree1")
		}

	})

	t.Run("TestCopy_pafx", func(t *testing.T) {

		tree3 := NewNode()
		tree4 := tree3.Copy()
		tree3 = tree3.Insert(pafx.(AST.Pred))
		res3 := tree4.IsEmpty()
		if !res3 {
			t.Fatalf("Tree4 is not a copy, it s only a pointer to tree3")
		}

	})

}

func TestUnify(t *testing.T) {

	t.Run("Unify_pax_with_pay", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))

		found, mix := tree.Unify(pay)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a, Y)" {
			t.Errorf("Expected unified form to be 'P(a, Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_pax_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))

		found, mix := tree.Unify(pab)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a, b)" {
			t.Errorf("Expected unified form to be 'P(a, b)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_pa_with_pa", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))

		found, mix := tree.Unify(pa)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a)" {
			t.Errorf("Expected unified form to be 'P(a)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_pax_with_pafy", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))

		found, mix := tree.Unify(pafy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected unified form to be 'P(a, f(Y))', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_pafx_with_pafy", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pafx.(AST.Pred))

		found, mix := tree.Unify(pafy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected unified form to be 'P(a, f(Y))', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_px_with_py", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(px.(AST.Pred))

		found, mix := tree.Unify(py)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(Y)" {
			t.Errorf("Expected unified form to be 'P(Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_pxy_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pxy.(AST.Pred))

		found, mix := tree.Unify(pab)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, b)" {
			t.Errorf("Expected unified form to be 'P(a, b)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify_Multiple_Inserts_with_py", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pb.(AST.Pred))
		tree = tree.Insert(pa.(AST.Pred))
		tree = tree.Insert(pfx.(AST.Pred))

		// P(Y) can unify with P(b), P(a), and P(f(x))
		found, mix := tree.Unify(py)

		if !found || len(mix) != 3 {
			t.Fatalf("Expected exactly 3 unification results, got %d", len(mix))
		}

		// Unification wraps the input formula
		for i, elem := range mix {
			if elem.GetForm().ToString() != "P(Y)" {
				t.Errorf("Expected unified form %d to be 'P(Y)', got '%s'", i, elem.GetForm().ToString())
			}
		}
	})

	t.Run("Unify_pggab_with_pxy", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pggab.(AST.Pred))

		found, mix := tree.Unify(pxy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(X, Y)" {
			t.Errorf("Expected unified form to be 'P(X, Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Exception_Unify_pa_with_pb", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))

		// Constants 'a' and 'b' cannot unify
		found, mix := tree.Unify(pb)

		if found {
			t.Errorf("Unification should have failed for P(a) and P(b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list, got %d elements", len(mix))
		}
	})

	t.Run("Exception_Unify_pxx_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pxx.(AST.Pred)) // P(x, x) requires both arguments to be identical

		found, mix := tree.Unify(pab) // P(a, b) has different arguments

		if found {
			t.Errorf("Unification should have failed: P(x, x) cannot unify with P(a, b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list")
		}
	})

	t.Run("Exception_Unify_pba_pab_with_pxx", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pba.(AST.Pred))
		tree = tree.Insert(pab.(AST.Pred))

		// P(X, X) requires identical arguments, neither P(b, a) nor P(a, b) fits
		found, mix := tree.Unify(pxx)

		if found {
			t.Errorf("Unification should have failed: P(X, X) cannot unify with P(b, a) or P(a, b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list")
		}
	})

	t.Run("Exception_Unify_pab_with_pxx", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))

		found, mix := tree.Unify(pxx)

		if found || len(mix) != 0 {
			t.Errorf("Unification should have failed: P(a, b) cannot unify with P(X, X)")
		}
	})
}
func TestUnifyTerm(t *testing.T) {

	t.Run("UnifyTerm_pax_with_pay", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		queryTerm := subst.TransformPred(pay.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
	})

	t.Run("UnifyTerm_pax_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, got %d", len(mix))
		}
	})

	t.Run("UnifyTerm_pa_with_pa", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		queryTerm := subst.TransformPred(pa.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, got %d", len(mix))
		}
		if mix[0].ToString() != "P(a) {}" {
			t.Errorf("Expected result 'P(a) {}', got '%s'", mix[0].ToString())
		}
	})

	t.Run("UnifyTerm_pab_with_pay", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pay.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, Y)" {
			t.Errorf("Expected term to be 'P(a, Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm_pafx_with_pafy", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pafx.(AST.Pred))
		queryTerm := subst.TransformPred(pafy.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected term to be 'P(a, f(Y))', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm_px_with_py", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(px.(AST.Pred))
		queryTerm := subst.TransformPred(py.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(Y)" {
			t.Errorf("Expected term to be 'P(Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm_pxy_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pxy.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, b)" {
			t.Errorf("Expected term to be 'P(a, b)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm_Multiple_Inserts_with_py", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pb.(AST.Pred))
		tree = tree.Insert(pa.(AST.Pred))
		tree = tree.Insert(pfx.(AST.Pred))
		queryTerm := subst.TransformPred(py.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success with matches")
		}
		if len(mix) != 3 {
			t.Fatalf("Expected exactly 3 unification results, got %d", len(mix))
		}
		for i, elem := range mix {
			if elem.Term().ToString() != "P(Y)" {
				t.Errorf("Expected unified term %d to be 'P(Y)', got '%s'", i, elem.Term().ToString())
			}
		}
	})

	t.Run("UnifyTerm_pggab_with_pxy", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pggab.(AST.Pred))
		queryTerm := subst.TransformPred(pxy.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(X, Y)" {
			t.Errorf("Expected term to be 'P(X, Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("Exception_UnifyTerm_pa_with_pb", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		queryTerm := subst.TransformPred(pb.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if val {
			t.Fatalf("Unification should have failed for P(a) and P(b)")
		}
		if len(mix) != 0 {
			t.Fatalf("Expected 0 elements, got %d", len(mix))
		}
	})

	t.Run("Exception_UnifyTerm_pxx_with_pab", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pxx.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if val || len(mix) != 0 {
			t.Fatalf("Unification should have failed: P(x,x) cannot unify with P(a,b)")
		}
	})

	t.Run("Exception_UnifyTerm_pba_pab_with_pxx", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pba.(AST.Pred))
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pxx.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if val {
			t.Fatalf("Unification should have failed: expected 0 elements, got %d", len(mix))
		}
	})

	t.Run("Exception_UnifyTerm_pab_with_pxx", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pxx.(AST.Pred))

		val, mix := tree.UnifyTerm(queryTerm)

		if val {
			t.Fatalf("Unification should have failed: expected 0 elements, got %d", len(mix))
		}
		if len(mix) != 0 {
			t.Fatalf("Expected result array to be empty, got %d elements", len(mix))
		}
	})
}

func TestMakeDataStruct(t *testing.T) {

	t.Run("MakeDataStruct_Positive_Tree", func(t *testing.T) {
		tree1 := NewNode()
		formulas1 := Lib.NewList[AST.Form]()
		formulas1.Append(pab)     // + => Inserted
		formulas1.Append(not_pac) // - => Ignored
		formulas1.Append(not_pba) // - => Ignored
		formulas1.Append(pba)     // + => Inserted

		actualTree1, ok := tree1.MakeDataStruct(formulas1, true).(*DiscriminationNode)
		if !ok {
			if directTree, okDirect := tree1.MakeDataStruct(formulas1, true).(DiscriminationNode); okDirect {
				actualTree1 = &directTree
			} else {
				t.Fatalf("MakeDataStruct didn't return a valid DiscriminationNode type")
			}
		}

		actualTree1.Print()

		rootChildren := actualTree1.getChildren().GetSlice()
		if len(rootChildren) != 1 {
			t.Fatalf("Expected exactly 1 predicate root node ('P'), got %d", len(rootChildren))
		}

		pNode := rootChildren[0]
		if pNode.getSymbol().getSymbol().ToString() != "P" {
			t.Errorf("Expected root node symbol to be 'P', got '%s'", pNode.getSymbol().getSymbol().ToString())
		}

		pChildren := pNode.getChildren().GetSlice()
		if len(pChildren) != 2 {
			t.Fatalf("Expected 'P' to have exactly 2 children ('a' and 'b') from positive formulas, got %d", len(pChildren))
		}

		for _, child := range pChildren {
			symStr := child.getSymbol().getSymbol().ToString()
			if symStr == "c" {
				t.Errorf("Negative formula 'not_pac' was incorrectly inserted into the positive tree")
			}
		}
	})

	t.Run("MakeDataStruct_Negative_Tree", func(t *testing.T) {

		tree2 := NewNode()
		formulas2 := Lib.NewList[AST.Form]()
		formulas2.Append(pab)     // + => Ignored
		formulas2.Append(not_pac) // - => Inserted
		formulas2.Append(not_pba) // - => Inserted
		formulas2.Append(pba)     // + => Ignored

		actualTree2, ok := tree2.MakeDataStruct(formulas2, false).(*DiscriminationNode)
		if !ok {
			if directTree, okDirect := tree2.MakeDataStruct(formulas2, false).(DiscriminationNode); okDirect {
				actualTree2 = &directTree
			} else {
				t.Fatalf("MakeDataStruct didn't return a valid DiscriminationNode type")
			}
		}

		actualTree2.Print()

		rootChildren := actualTree2.getChildren().GetSlice()
		if len(rootChildren) != 1 {
			t.Fatalf("Expected exactly 1 predicate root node ('P'), got %d", len(rootChildren))
		}

		pNode := rootChildren[0]
		pChildren := pNode.getChildren().GetSlice()
		if len(pChildren) == 0 {
			t.Fatalf("Negative tree is empty, expected nodes from negative formulas")
		}
	})
}
func TestUnify2(t *testing.T) {

	t.Run("Unify2_pax_with_pay", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))

		found, mix := tree.Unify2(pay)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a, Y)" {
			t.Errorf("Expected unified form to be 'P(a, Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_pax_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		found, mix := tree.Unify2(pab)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a, b)" {
			t.Errorf("Expected unified form to be 'P(a, b)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_pa_with_pa", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		found, mix := tree.Unify2(pa)

		if !found {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
		if mix[0].GetForm().ToString() != "P(a)" {
			t.Errorf("Expected unified form to be 'P(a)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_pax_with_pafy", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		found, mix := tree.Unify2(pafy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected unified form to be 'P(a, f(Y))', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_pafx_with_pafy", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pafx.(AST.Pred))
		found, mix := tree.Unify2(pafy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected unified form to be 'P(a, f(Y))', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_px_with_py", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(px.(AST.Pred))
		found, mix := tree.Unify2(py)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(Y)" {
			t.Errorf("Expected unified form to be 'P(Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_pxy_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pxy.(AST.Pred))
		found, mix := tree.Unify2(pab)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(a, b)" {
			t.Errorf("Expected unified form to be 'P(a, b)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Unify2_Multiple_Inserts_with_py", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pb.(AST.Pred))
		tree = tree.Insert(pa.(AST.Pred))
		tree = tree.Insert(pfx.(AST.Pred))
		found, mix := tree.Unify2(py)

		if !found || len(mix) != 3 {
			t.Fatalf("Expected exactly 3 unification results, got %d", len(mix))
		}

		for i, elem := range mix {
			if elem.GetForm().ToString() != "P(Y)" {
				t.Errorf("Expected unified form %d to be 'P(Y)', got '%s'", i, elem.GetForm().ToString())
			}
		}
	})

	t.Run("Unify2_pggab_with_pxy", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pggab.(AST.Pred))
		found, mix := tree.Unify2(pxy)

		if !found || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result")
		}
		if mix[0].GetForm().ToString() != "P(X, Y)" {
			t.Errorf("Expected unified form to be 'P(X, Y)', got '%s'", mix[0].GetForm().ToString())
		}
	})

	t.Run("Exception_Unify2_pa_with_pb", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		found, mix := tree.Unify2(pb)

		if found {
			t.Errorf("Unification should have failed for P(a) and P(b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list, got %d elements", len(mix))
		}
	})

	t.Run("Exception_Unify2_pxx_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pxx.(AST.Pred))
		found, mix := tree.Unify2(pab)

		if found {
			t.Errorf("Unification should have failed: P(x, x) cannot unify with P(a, b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list")
		}
	})

	t.Run("Exception_Unify2_pba_pab_with_pxx", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pba.(AST.Pred))
		tree = tree.Insert(pab.(AST.Pred))
		found, mix := tree.Unify2(pxx)

		if found {
			t.Errorf("Unification should have failed: P(X, X) cannot unify with P(b, a) or P(a, b)")
		}
		if len(mix) != 0 {
			t.Errorf("Expected empty result list")
		}
	})

	t.Run("Exception_Unify2_pab_with_pxx", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		found, mix := tree.Unify2(pxx)

		if found || len(mix) != 0 {
			t.Errorf("Unification should have failed: P(a, b) cannot unify with P(X, X)")
		}
	})
}

func TestUnifyTerm2(t *testing.T) {

	t.Run("UnifyTerm2_pax_with_pay", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		queryTerm := subst.TransformPred(pay.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 unification result, got %d", len(mix))
		}
	})

	t.Run("UnifyTerm2_pax_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pax.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, got %d", len(mix))
		}
	})

	t.Run("UnifyTerm2_pa_with_pa", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		queryTerm := subst.TransformPred(pa.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success")
		}
		if len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, got %d", len(mix))
		}
		if mix[0].ToString() != "P(a) {}" {
			t.Errorf("Expected result 'P(a) {}', got '%s'", mix[0].ToString())
		}
	})

	t.Run("UnifyTerm2_pab_with_pay", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pay.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, Y)" {
			t.Errorf("Expected term to be 'P(a, Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm2_pafx_with_pafy", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pafx.(AST.Pred))
		queryTerm := subst.TransformPred(pafy.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, f(Y))" {
			t.Errorf("Expected term to be 'P(a, f(Y))', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm2_px_with_py", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(px.(AST.Pred))
		queryTerm := subst.TransformPred(py.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(Y)" {
			t.Errorf("Expected term to be 'P(Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm2_pxy_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pxy.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(a, b)" {
			t.Errorf("Expected term to be 'P(a, b)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("UnifyTerm2_Multiple_Inserts_with_py", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pb.(AST.Pred))
		tree = tree.Insert(pa.(AST.Pred))
		tree = tree.Insert(pfx.(AST.Pred))
		queryTerm := subst.TransformPred(py.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val {
			t.Fatalf("Unification failed, expected success with matches")
		}
		if len(mix) != 3 {
			t.Fatalf("Expected exactly 3 unification results, got %d", len(mix))
		}
		for i, elem := range mix {
			if elem.Term().ToString() != "P(Y)" {
				t.Errorf("Expected unified term %d to be 'P(Y)', got '%s'", i, elem.Term().ToString())
			}
		}
	})

	t.Run("UnifyTerm2_pggab_with_pxy", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pggab.(AST.Pred))
		queryTerm := subst.TransformPred(pxy.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if !val || len(mix) != 1 {
			t.Fatalf("Expected exactly 1 result, found valid=%t, len=%d", val, len(mix))
		}
		if mix[0].Term().ToString() != "P(X, Y)" {
			t.Errorf("Expected term to be 'P(X, Y)', got '%s'", mix[0].Term().ToString())
		}
	})

	t.Run("Exception_UnifyTerm2_pa_with_pb", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pa.(AST.Pred))
		queryTerm := subst.TransformPred(pb.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if val {
			t.Fatalf("Unification should have failed for P(a) and P(b)")
		}
		if len(mix) != 0 {
			t.Fatalf("Expected 0 elements, got %d", len(mix))
		}
	})

	t.Run("Exception_UnifyTerm2_pxx_with_pab", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pxx.(AST.Pred))
		queryTerm := subst.TransformPred(pab.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if val || len(mix) != 0 {
			t.Fatalf("Unification should have failed: P(x,x) cannot unify with P(a,b)")
		}
	})

	t.Run("Exception_UnifyTerm2_pba_pab_with_pxx", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pba.(AST.Pred))
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pxx.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if val {
			t.Fatalf("Unification should have failed: expected 0 elements, got %d", len(mix))
		}
	})

	t.Run("Exception_UnifyTerm2_pab_with_pxx", func(t *testing.T) {

		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))
		queryTerm := subst.TransformPred(pxx.(AST.Pred))

		val, mix := tree.UnifyTerm2(queryTerm)

		if val {
			t.Fatalf("Unification should have failed: expected 0 elements, got %d", len(mix))
		}
		if len(mix) != 0 {
			t.Fatalf("Expected result array to be empty, got %d elements", len(mix))
		}
	})
}

func TestContextStange(t *testing.T) {

	t.Run("Exception_Occur_Check_Cyclic", func(t *testing.T) {
		tree := NewNode()
		tree.Insert(pfx.(AST.Pred))
		val, mix := tree.Unify(px)

		if val {
			t.Fatalf("Occur Check Faillure")
		}
		if len(mix) != 0 {
			t.Fatalf("Occur Check Faillure")
		}
	})

	t.Run("UnifyTerm_Complex_SkipTerm", func(t *testing.T) {
		tree := NewNode()
		tree.Insert(pfgaba.(AST.Pred))
		val, mix := tree.Unify(px)

		if val {
			t.Fatalf("Occur Check Faillure")
		}
		if len(mix) != 0 {
			t.Fatalf("Occur Check Faillure")
		}
	})

	t.Run("Exception_Shared_Query_Variables", func(t *testing.T) {
		tree := NewNode()
		tree = tree.Insert(pab.(AST.Pred))

		queryTerm := subst.TransformPred(pxx.(AST.Pred))
		val, _ := tree.UnifyTerm(queryTerm)

		if val {
			t.Fatalf("Unification should fail because X cannot be 'a' and 'b' simultaneously")
		}
	})

}
