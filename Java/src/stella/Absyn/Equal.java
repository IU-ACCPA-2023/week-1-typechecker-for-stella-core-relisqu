// File generated by the BNF Converter (bnfc 2.9.4.1).

package stella.Absyn;

public class Equal  extends Expr {
  public final Expr expr_1, expr_2;
  public int line_num, col_num, offset;
  public Equal(Expr p1, Expr p2) { expr_1 = p1; expr_2 = p2; }

  public <R,A> R accept(stella.Absyn.Expr.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof stella.Absyn.Equal) {
      stella.Absyn.Equal x = (stella.Absyn.Equal)o;
      return this.expr_1.equals(x.expr_1) && this.expr_2.equals(x.expr_2);
    }
    return false;
  }

  public int hashCode() {
    return 37*(this.expr_1.hashCode())+this.expr_2.hashCode();
  }


}
