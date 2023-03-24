// File generated by the BNF Converter (bnfc 2.9.4.1).

package stella.Absyn;

public abstract class Type implements java.io.Serializable {
  public abstract <R,A> R accept(Type.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(stella.Absyn.TypeFun p, A arg);
    public R visit(stella.Absyn.TypeRec p, A arg);
    public R visit(stella.Absyn.TypeSum p, A arg);
    public R visit(stella.Absyn.TypeTuple p, A arg);
    public R visit(stella.Absyn.TypeRecord p, A arg);
    public R visit(stella.Absyn.TypeVariant p, A arg);
    public R visit(stella.Absyn.TypeList p, A arg);
    public R visit(stella.Absyn.TypeBool p, A arg);
    public R visit(stella.Absyn.TypeNat p, A arg);
    public R visit(stella.Absyn.TypeUnit p, A arg);
    public R visit(stella.Absyn.TypeVar p, A arg);

  }

}