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

// Form
var pggab AST.Form
var pac AST.Form
var pa AST.Form
var pb AST.Form
var not_pc AST.Form
var pab AST.Form
var pax AST.Form
var not_pcd AST.Form

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
	gx = AST.MakerFun(g_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	ga = AST.MakerFun(g_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))
	fx = AST.MakerFun(f_id, Lib.MkListV(x.GetTy()), Lib.MkListV[AST.Term](x))
	fy = AST.MakerFun(f_id, Lib.MkListV(y.GetTy()), Lib.MkListV[AST.Term](y))
	fa = AST.MakerFun(f_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))
	fb = AST.MakerFun(f_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))
	fc = AST.MakerFun(f_id, c.GetTyArgs(), Lib.MkListV[AST.Term](c))

	ggx = AST.MakerFun(g_id, gx.GetTyArgs(), Lib.MkListV[AST.Term](gx))
	gga = AST.MakerFun(g_id, ga.GetTyArgs(), Lib.MkListV[AST.Term](ga))
	gfy = AST.MakerFun(g_id, fy.GetTyArgs(), Lib.MkListV[AST.Term](fy))
	gfa = AST.MakerFun(g_id, fa.GetTyArgs(), Lib.MkListV[AST.Term](fa))
	fxy = AST.MakerFun(f_id, Lib.MkListV(x.GetTy(), y.GetTy()), Lib.MkListV[AST.Term](x, y))
	fyz = AST.MakerFun(f_id, Lib.MkListV(x.GetTy(), z.GetTy()), Lib.MkListV[AST.Term](x, z))
	ffx = AST.MakerFun(f_id, fx.GetTyArgs(), Lib.MkListV[AST.Term](fx))

	x_a_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	x_a_type_list.Append(a.GetTyArgs().GetSlice()...)
	fxa = AST.MakerFun(f_id, x_a_type_list, Lib.MkListV[AST.Term](x, a))

	a_y_type_list := a.GetTyArgs()
	a_y_type_list.Append(y.GetTy())
	fay = AST.MakerFun(f_id, a_y_type_list, Lib.MkListV[AST.Term](a, y))

	a_b_type_list := a.GetTyArgs()
	a_b_type_list.Append(b.GetTyArgs().GetSlice()...)
	fab = AST.MakerFun(f_id, a_b_type_list, Lib.MkListV[AST.Term](a, b))

	bc_type_list := b.GetTyArgs()
	bc_type_list.Append(c.GetTyArgs().GetSlice()...)
	fbc = AST.MakerFun(f_id, bc_type_list, Lib.MkListV[AST.Term](b, c))

	cd_type_list := c.GetTyArgs()
	cd_type_list.Append(d.GetTyArgs().GetSlice()...)
	fcd = AST.MakerFun(f_id, cd_type_list, Lib.MkListV[AST.Term](c, d))

	gggx = AST.MakerFun(g_id, ggx.GetTyArgs(), Lib.MkListV[AST.Term](ggx))

	fxy_z_type_list := fxy.GetTyArgs()
	fxy_z_type_list.Append(z.GetTy())
	f_fxy_z = AST.MakerFun(f_id, fxy_z_type_list, Lib.MkListV[AST.Term](fxy, z))

	x_fyz_type_list := Lib.MkListV[AST.Ty](x.GetTy())
	x_fyz_type_list.Append(fyz.GetTyArgs().GetSlice()...)
	f_x_fyz = AST.MakerFun(f_id, x_fyz_type_list, Lib.MkListV[AST.Term](x, fyz))

	fab_c_type_list := fab.GetTyArgs()
	fab_c_type_list.Append(c.GetTyArgs().GetSlice()...)
	f_fab_c = AST.MakerFun(f_id, fab_c_type_list, Lib.MkListV[AST.Term](fab, c))

	a_fbc_type_list := a.GetTyArgs()
	a_fbc_type_list.Append(fbc.GetTyArgs().GetSlice()...)
	f_a_fbc = AST.MakerFun(f_id, a_fbc_type_list, Lib.MkListV[AST.Term](a, fbc))

	// Predicates
	pggab_type_list := gga.GetTyArgs()
	pggab_type_list.Append(b.GetTyArgs().GetSlice()...)
	pggab = AST.MakerPred(p_id, pggab_type_list, Lib.MkListV[AST.Term](gga, b))

	pac_type_list := a.GetTyArgs()
	pac_type_list.Append(c.GetTyArgs().GetSlice()...)
	pac = AST.MakerNot(AST.MakerPred(p_id, pac_type_list, Lib.MkListV[AST.Term](a, c)))

	pa = AST.MakerPred(p_id, a.GetTyArgs(), Lib.MkListV[AST.Term](a))

	pb = AST.MakerPred(p_id, b.GetTyArgs(), Lib.MkListV[AST.Term](b))

	not_pc = AST.MakerNot(AST.MakerPred(p_id, c.GetTyArgs(), Lib.MkListV[AST.Term](c)))

	pab_type_list := a.GetTyArgs()
	pab_type_list.Append(b.GetTyArgs().GetSlice()...)
	pab = AST.MakerPred(p_id, pab_type_list, Lib.MkListV[AST.Term](a, b))

	pax_type_list := a.GetTyArgs()
	pax_type_list.Append(x.GetTy())
	pax = AST.MakerPred(p_id, pax_type_list, Lib.MkListV[AST.Term](a, x))

	not_pcd_type_list := c.GetTyArgs()
	not_pcd_type_list.Append(d.GetTyArgs().GetSlice()...)
	not_pcd = AST.MakerNot(AST.MakerPred(p_id, not_pcd_type_list, Lib.MkListV[AST.Term](c, d)))
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

func TestPrintDiscriminationTree(t *testing.T) {
	tree := NewNode()
	tree = tree.Insert(ggx)
	fmt.Println(tree.DisplayDiscriminationTree())

	tree2 := NewNode()
	tree2 = tree2.Insert(fxy)
	fmt.Println(tree2.DisplayDiscriminationTree())

}
