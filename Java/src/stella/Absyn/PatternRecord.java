// File generated by the BNF Converter (bnfc 2.9.4.1).

package stella.Absyn;

public class PatternRecord  extends Pattern {
  public final ListLabelledPattern listlabelledpattern_;
  public int line_num, col_num, offset;
  public PatternRecord(ListLabelledPattern p1) { listlabelledpattern_ = p1; }

  public <R,A> R accept(stella.Absyn.Pattern.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof stella.Absyn.PatternRecord) {
      stella.Absyn.PatternRecord x = (stella.Absyn.PatternRecord)o;
      return this.listlabelledpattern_.equals(x.listlabelledpattern_);
    }
    return false;
  }

  public int hashCode() {
    return this.listlabelledpattern_.hashCode();
  }


}