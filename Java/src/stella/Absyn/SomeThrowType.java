// File generated by the BNF Converter (bnfc 2.9.4.1).

package stella.Absyn;

public class SomeThrowType  extends ThrowType {
  public final ListType listtype_;
  public int line_num, col_num, offset;
  public SomeThrowType(ListType p1) { listtype_ = p1; }

  public <R,A> R accept(stella.Absyn.ThrowType.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof stella.Absyn.SomeThrowType) {
      stella.Absyn.SomeThrowType x = (stella.Absyn.SomeThrowType)o;
      return this.listtype_.equals(x.listtype_);
    }
    return false;
  }

  public int hashCode() {
    return this.listtype_.hashCode();
  }


}
