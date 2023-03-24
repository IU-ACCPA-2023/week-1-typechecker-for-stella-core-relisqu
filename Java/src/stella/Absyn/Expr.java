// File generated by the BNF Converter (bnfc 2.9.4.1).

package stella.Absyn;

public abstract class Expr implements java.io.Serializable {
  public abstract <R,A> R accept(Expr.Visitor<R,A> v, A arg);
  public interface Visitor <R,A> {
    public R visit(stella.Absyn.If p, A arg);
    public R visit(stella.Absyn.Let p, A arg);
    public R visit(stella.Absyn.LessThan p, A arg);
    public R visit(stella.Absyn.LessThanOrEqual p, A arg);
    public R visit(stella.Absyn.GreaterThan p, A arg);
    public R visit(stella.Absyn.GreaterThanOrEqual p, A arg);
    public R visit(stella.Absyn.Equal p, A arg);
    public R visit(stella.Absyn.NotEqual p, A arg);
    public R visit(stella.Absyn.TypeAsc p, A arg);
    public R visit(stella.Absyn.Abstraction p, A arg);
    public R visit(stella.Absyn.Tuple p, A arg);
    public R visit(stella.Absyn.Record p, A arg);
    public R visit(stella.Absyn.Variant p, A arg);
    public R visit(stella.Absyn.Match p, A arg);
    public R visit(stella.Absyn.List p, A arg);
    public R visit(stella.Absyn.Add p, A arg);
    public R visit(stella.Absyn.LogicOr p, A arg);
    public R visit(stella.Absyn.Multiply p, A arg);
    public R visit(stella.Absyn.LogicAnd p, A arg);
    public R visit(stella.Absyn.Application p, A arg);
    public R visit(stella.Absyn.ConsList p, A arg);
    public R visit(stella.Absyn.Head p, A arg);
    public R visit(stella.Absyn.IsEmpty p, A arg);
    public R visit(stella.Absyn.Tail p, A arg);
    public R visit(stella.Absyn.Succ p, A arg);
    public R visit(stella.Absyn.LogicNot p, A arg);
    public R visit(stella.Absyn.Pred p, A arg);
    public R visit(stella.Absyn.IsZero p, A arg);
    public R visit(stella.Absyn.Fix p, A arg);
    public R visit(stella.Absyn.NatRec p, A arg);
    public R visit(stella.Absyn.Fold p, A arg);
    public R visit(stella.Absyn.Unfold p, A arg);
    public R visit(stella.Absyn.DotRecord p, A arg);
    public R visit(stella.Absyn.DotTuple p, A arg);
    public R visit(stella.Absyn.ConstTrue p, A arg);
    public R visit(stella.Absyn.ConstFalse p, A arg);
    public R visit(stella.Absyn.ConstInt p, A arg);
    public R visit(stella.Absyn.Var p, A arg);

  }

}