/**
 * Provides the shared CFG library instantiation for Go.
 *
 * Everything is wrapped in `GoCfg` to avoid name conflicts with the existing
 * CFG implementation during the transition.
 */
overlay[local?]
module;

private import codeql.controlflow.ControlFlowGraph as CfgLib
private import codeql.controlflow.SuccessorType

/** Contains the shared CFG library instantiation for Go. */
module GoCfg {
  private import go as Go

  private module Cfg0 = CfgLib::Make0<Go::Location, Ast>;

  private module Cfg1 = Cfg0::Make1<Input>;

  private module Cfg2 = Cfg1::Make2<Input>;

  private import Cfg0
  private import Cfg1
  private import Cfg2
  import Public

  /** Provides an implementation of the AST signature for Go. */
  private module Ast implements CfgLib::AstSig<Go::Location> {
    class AstNode = Go::AstNode;

    private predicate skipCfg(AstNode e) {
      e instanceof Go::TypeExpr and not e instanceof Go::FuncTypeExpr
      or
      e = any(Go::FieldDecl f).getTag()
      or
      e instanceof Go::KeyValueExpr and not e = any(Go::CompositeLit lit).getAnElement()
      or
      e = any(Go::SelectorExpr sel).getSelector()
      or
      e = any(Go::StructLit sl).getKey(_)
      or
      e instanceof Go::Ident and not e instanceof Go::ReferenceExpr
      or
      e instanceof Go::SelectorExpr and not e instanceof Go::ReferenceExpr
      or
      e instanceof Go::ReferenceExpr and not e.(Go::ReferenceExpr).isRvalue()
      or
      e instanceof Go::ParenExpr
      or
      e = any(Go::ImportSpec is).getPathExpr()
      or
      e.getParent*() = any(Go::ArrayTypeExpr ate).getLength()
    }

    AstNode getChild(AstNode n, int index) {
      not skipCfg(result) and not skipCfg(n) and result = n.getChild(index)
    }

    class Callable extends AstNode {
      Callable() { exists(this.(Go::FuncDef).getBody()) }
    }

    AstNode callableGetBody(Callable c) { result = c.(Go::FuncDef).getBody() }

    Callable getEnclosingCallable(AstNode node) { result = node.getEnclosingFunction() }

    class Stmt = Go::Stmt;

    class Expr = Go::Expr;

    class BlockStmt extends Go::BlockStmt {
      BlockStmt() {
        not this = any(Go::SwitchStmt sw).getBody() and
        not this = any(Go::SelectStmt sel).getBody()
      }

      override Stmt getStmt(int n) { result = Go::BlockStmt.super.getStmt(n) }

      Stmt getLastStmt() {
        exists(int last | result = this.getStmt(last) and not exists(this.getStmt(last + 1)))
      }
    }

    class ExprStmt = Go::ExprStmt;

    /** If statements without init (those with init use custom steps). */
    class IfStmt extends Stmt {
      IfStmt() { this instanceof Go::IfStmt and not exists(this.(Go::IfStmt).getInit()) }

      Expr getCondition() { result = this.(Go::IfStmt).getCond() }

      Stmt getThen() { result = this.(Go::IfStmt).getThen() }

      Stmt getElse() { result = this.(Go::IfStmt).getElse() }
    }

    class LoopStmt extends Stmt {
      LoopStmt() { this instanceof Go::LoopStmt }

      Stmt getBody() { result = this.(Go::LoopStmt).getBody() }
    }

    class WhileStmt extends LoopStmt {
      WhileStmt() { none() }

      Expr getCondition() { none() }
    }

    class DoStmt extends LoopStmt {
      DoStmt() { none() }

      Expr getCondition() { none() }
    }

    class ForStmt extends LoopStmt {
      ForStmt() { none() }

      Expr getInit(int index) { none() }

      Expr getCondition() { none() }

      Expr getUpdate(int index) { none() }
    }

    class ForeachStmt extends LoopStmt {
      ForeachStmt() { none() }

      Expr getVariable() { none() }

      Expr getCollection() { none() }
    }

    class BreakStmt = Go::BreakStmt;

    class ContinueStmt = Go::ContinueStmt;

    class ReturnStmt extends Go::ReturnStmt {
      override Expr getExpr() { result = Go::ReturnStmt.super.getExpr() }
    }

    class ThrowStmt extends Stmt {
      ThrowStmt() { none() }

      Expr getExpr() { none() }
    }

    class TryStmt extends Stmt {
      TryStmt() { none() }

      Stmt getBody() { none() }

      CatchClause getCatch(int index) { none() }

      Stmt getFinally() { none() }
    }

    class CatchClause extends AstNode {
      CatchClause() { none() }

      AstNode getVariable() { none() }

      Expr getCondition() { none() }

      Stmt getBody() { none() }
    }

    class Switch extends AstNode {
      Switch() { none() }

      Expr getExpr() { none() }

      Case getCase(int index) { none() }

      Stmt getStmt(int index) { none() }
    }

    class Case extends AstNode {
      Case() { none() }

      AstNode getAPattern() { none() }

      Expr getGuard() { none() }

      AstNode getBody() { none() }
    }

    class DefaultCase extends Case {
      DefaultCase() { none() }
    }

    class ConditionalExpr extends Expr {
      ConditionalExpr() { none() }

      Expr getCondition() { none() }

      Expr getThen() { none() }

      Expr getElse() { none() }
    }

    class BinaryExpr = Go::BinaryExpr;

    class LogicalAndExpr = Go::LandExpr;

    class LogicalOrExpr = Go::LorExpr;

    class NullCoalescingExpr extends BinaryExpr {
      NullCoalescingExpr() { none() }
    }

    class UnaryExpr = Go::UnaryExpr;

    class LogicalNotExpr = Go::NotExpr;

    class BooleanLiteral extends Expr {
      boolean val;

      BooleanLiteral() {
        this.(Go::Ident).getName() = "true" and val = true
        or
        this.(Go::Ident).getName() = "false" and val = false
      }

      boolean getValue() { result = val }
    }
  }

  /** The Input module implementing InputSig1 and InputSig2 for Go. */
  private module Input implements Cfg0::InputSig1, Cfg1::InputSig2 {
    predicate cfgCachedStageRef() { CfgCachedStage::ref() }

    private newtype TLabel =
      TGoLabel(string l) { exists(Go::LabeledStmt ls | l = ls.getLabel()) } or
      TFallthrough()

    class Label extends TLabel {
      string toString() {
        exists(string l | this = TGoLabel(l) and result = l)
        or
        this = TFallthrough() and result = "fallthrough"
      }
    }

    private Label getLabelOfStmt(Go::Stmt s) {
      exists(Go::LabeledStmt l | s = l.getStmt() |
        result = TGoLabel(l.getLabel()) or result = getLabelOfStmt(l)
      )
    }

    predicate hasLabel(Ast::AstNode n, Label l) {
      l = getLabelOfStmt(n)
      or
      l = TGoLabel(n.(Go::BreakStmt).getLabel())
      or
      l = TGoLabel(n.(Go::ContinueStmt).getLabel())
      or
      l = TFallthrough() and n instanceof Go::FallthroughStmt
    }

    predicate inConditionalContext(Ast::AstNode n, ConditionKind kind) {
      kind.isBoolean() and
      (
        exists(Go::IfStmt ifstmt | ifstmt.getCond() = n and exists(ifstmt.getInit()))
        or
        n = any(Go::ForStmt fs).getCond()
        or
        exists(Go::ExpressionSwitchStmt ess |
          not exists(ess.getExpr()) and n = ess.getACase().(Go::CaseClause).getExpr(_)
        )
      )
    }

    predicate preOrderExpr(Ast::Expr e) { none() }

    predicate postOrInOrder(Ast::AstNode n) {
      n instanceof Go::CallExpr and
      not n = any(Go::DeferStmt defer).getCall() and
      not n = any(Go::GoStmt go_).getCall()
      or
      n instanceof Go::BinaryExpr and not n instanceof Go::LogicalBinaryExpr
      or
      n instanceof Go::UnaryExpr and not n instanceof Go::NotExpr
      or
      n instanceof Go::ConversionExpr
      or
      n instanceof Go::TypeAssertExpr
      or
      n instanceof Go::IndexExpr
      or
      n instanceof Go::SliceExpr
      or
      n instanceof Go::CompositeLit
      or
      n instanceof Go::ReturnStmt
      or
      n instanceof Go::DeferStmt
      or
      n instanceof Go::GoStmt
      or
      n instanceof Go::SendStmt
      or
      n instanceof Go::IncDecStmt
      or
      n instanceof Go::FuncDecl
      or
      n instanceof Go::SelectorExpr and
      n.(Go::SelectorExpr).getBase() instanceof Go::ValueExpr
    }

    predicate additionalNode(Ast::AstNode n, string tag, NormalSuccessor t) { none() }

    predicate beginAbruptCompletion(
      Ast::AstNode ast, PreControlFlowNode n, AbruptCompletion c, boolean always
    ) {
      ast instanceof Go::CallExpr and
      (
        not exists(ast.(Go::CallExpr).getTarget()) or
        ast.(Go::CallExpr).getTarget().mayPanic()
      ) and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::DivExpr and
      not ast.(Go::Expr).isConst() and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::DerefExpr and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::TypeAssertExpr and
      not exists(Go::Assignment assgn |
        assgn.getNumLhs() = 2 and ast = assgn.getRhs().stripParens()
      ) and
      not exists(Go::ValueSpec vs | vs.getNumName() = 2 and ast = vs.getInit().stripParens()) and
      not exists(Go::TypeSwitchStmt ts | ast = ts.getExpr()) and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::IndexExpr and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::ConversionExpr and
      ast.(Go::ConversionExpr).getType().(Go::PointerType).getBaseType() instanceof Go::ArrayType and
      n.isIn(ast) and
      c.asSimpleAbruptCompletion() instanceof ExceptionSuccessor and
      always = false
      or
      ast instanceof Go::FallthroughStmt and
      n.injects(ast) and
      c.getSuccessorType() instanceof BreakSuccessor and
      c.hasLabel(TFallthrough()) and
      always = true
      or
      ast instanceof Go::GotoStmt and
      n.injects(ast) and
      c.getSuccessorType() instanceof GotoSuccessor and
      c.hasLabel(TGoLabel(ast.(Go::GotoStmt).getLabel())) and
      always = true
    }

    predicate endAbruptCompletion(Ast::AstNode ast, PreControlFlowNode n, AbruptCompletion c) {
      exists(Go::LabeledStmt lbl |
        ast = lbl.getStmt() and
        n.isAfter(lbl) and
        c.getSuccessorType() instanceof BreakSuccessor and
        c.hasLabel(TGoLabel(lbl.getLabel()))
      )
      or
      exists(Go::LabeledStmt lbl, Go::FuncDef fd |
        ast = fd.getBody() and
        n.isBefore(lbl) and
        fd = lbl.getEnclosingFunction() and
        c.getSuccessorType() instanceof GotoSuccessor and
        c.hasLabel(TGoLabel(lbl.getLabel()))
      )
    }

    predicate step(PreControlFlowNode n1, PreControlFlowNode n2) {
      ifWithInit(n1, n2) or
      forLoop(n1, n2) or
      rangeLoop(n1, n2) or
      switchStmt(n1, n2) or
      selectStmt(n1, n2) or
      deferStmt(n1, n2) or
      goStmtStep(n1, n2)
    }

    private predicate ifWithInit(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::IfStmt s | exists(s.getInit()) |
        n1.isBefore(s) and n2.isBefore(s.getInit())
        or
        n1.isAfter(s.getInit()) and n2.isBefore(s.getCond())
        or
        n1.isAfterTrue(s.getCond()) and n2.isBefore(s.getThen())
        or
        n1.isAfterFalse(s.getCond()) and
        (
          n2.isBefore(s.getElse())
          or
          not exists(s.getElse()) and n2.isAfter(s)
        )
        or
        n1.isAfter(s.getThen()) and n2.isAfter(s)
        or
        n1.isAfter(s.getElse()) and n2.isAfter(s)
      )
    }

    private predicate forLoop(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::ForStmt s |
        exists(PreControlFlowNode cond |
          (
            cond.isBefore(s.getCond())
            or
            not exists(s.getCond()) and cond.isBefore(s.getBody())
          )
        |
          n1.isBefore(s) and
          (
            n2.isBefore(s.getInit())
            or
            not exists(s.getInit()) and n2 = cond
          )
          or
          n1.isAfter(s.getInit()) and n2 = cond
          or
          n1.isAfterTrue(s.getCond()) and n2.isBefore(s.getBody())
          or
          n1.isAfterFalse(s.getCond()) and n2.isAfter(s)
          or
          not exists(s.getCond()) and
          n1.isAfter(s.getBody()) and
          (
            n2.isBefore(s.getPost())
            or
            not exists(s.getPost()) and n2.isBefore(s.getBody())
          )
          or
          exists(s.getCond()) and
          n1.isAfter(s.getBody()) and
          (
            n2.isBefore(s.getPost())
            or
            not exists(s.getPost()) and n2 = cond
          )
          or
          n1.isAfter(s.getPost()) and n2 = cond
        )
      )
    }

    private predicate rangeLoop(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::RangeStmt s |
        n1.isBefore(s) and n2.isBefore(s.getDomain())
        or
        n1.isAfter(s.getDomain()) and n2.isIn(s)
        or
        n1.isIn(s) and
        (
          n2.isBefore(s.getKey())
          or
          not exists(s.getKey()) and n2.isBefore(s.getBody())
        )
        or
        n1.isAfter(s.getKey()) and
        (
          n2.isBefore(s.getValue())
          or
          not exists(s.getValue()) and n2.isBefore(s.getBody())
        )
        or
        n1.isAfter(s.getValue()) and n2.isBefore(s.getBody())
        or
        n1.isAfter(s.getBody()) and n2.isIn(s)
        or
        n1.isIn(s) and n2.isAfter(s)
      )
    }

    private predicate switchStmt(PreControlFlowNode n1, PreControlFlowNode n2) {
      exprSwitch(n1, n2) or typeSwitch(n1, n2) or caseClause(n1, n2)
    }

    private predicate exprSwitch(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::ExpressionSwitchStmt sw |
        n1.isBefore(sw) and
        (
          n2.isBefore(sw.getInit())
          or
          not exists(sw.getInit()) and
          (
            n2.isBefore(sw.getExpr())
            or
            not exists(sw.getExpr()) and
            (
              n2.isBefore(sw.getNonDefaultCase(0))
              or
              not exists(sw.getANonDefaultCase()) and n2.isBefore(sw.getDefault())
              or
              not exists(sw.getACase()) and n2.isAfter(sw)
            )
          )
        )
        or
        n1.isAfter(sw.getInit()) and
        (
          n2.isBefore(sw.getExpr())
          or
          not exists(sw.getExpr()) and
          (
            n2.isBefore(sw.getNonDefaultCase(0))
            or
            not exists(sw.getANonDefaultCase()) and n2.isBefore(sw.getDefault())
          )
        )
        or
        n1.isAfter(sw.getExpr()) and
        (
          n2.isBefore(sw.getNonDefaultCase(0))
          or
          not exists(sw.getANonDefaultCase()) and n2.isBefore(sw.getDefault())
        )
      )
    }

    private predicate typeSwitch(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::TypeSwitchStmt sw |
        n1.isBefore(sw) and
        (
          n2.isBefore(sw.getInit())
          or
          not exists(sw.getInit()) and n2.isBefore(sw.getTest())
        )
        or
        n1.isAfter(sw.getInit()) and n2.isBefore(sw.getTest())
        or
        n1.isAfter(sw.getTest()) and
        (
          n2.isBefore(sw.getNonDefaultCase(0))
          or
          not exists(sw.getANonDefaultCase()) and n2.isBefore(sw.getDefault())
        )
      )
    }

    private predicate caseClause(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::SwitchStmt sw, Go::CaseClause cc, int i | cc = sw.getNonDefaultCase(i) |
        n1.isBefore(cc) and n2.isBefore(cc.getExpr(0))
        or
        exists(int j | n1.isAfter(cc.getExpr(j)) and n2.isBefore(cc.getExpr(j + 1)))
        or
        exists(int last | last = max(int j | exists(cc.getExpr(j))) |
          n1.isAfter(cc.getExpr(last)) and
          (
            n2.isBefore(cc.getStmt(0))
            or
            not exists(cc.getStmt(0)) and n2.isAfter(sw)
            or
            n2.isBefore(sw.getNonDefaultCase(i + 1))
            or
            not exists(sw.getNonDefaultCase(i + 1)) and n2.isBefore(sw.getDefault())
            or
            not exists(sw.getNonDefaultCase(i + 1)) and
            not exists(sw.getDefault()) and
            n2.isAfter(sw)
          )
        )
      )
      or
      exists(Go::SwitchStmt sw, Go::CaseClause def | def = sw.getDefault() |
        n1.isBefore(def) and
        (
          n2.isBefore(def.getStmt(0))
          or
          not exists(def.getStmt(0)) and n2.isAfter(sw)
        )
      )
      or
      exists(Go::CaseClause cc |
        exists(int j | n1.isAfter(cc.getStmt(j)) and n2.isBefore(cc.getStmt(j + 1)))
        or
        exists(Go::SwitchStmt sw, int last |
          sw.getACase() = cc and
          last = max(int j | exists(cc.getStmt(j))) and
          n1.isAfter(cc.getStmt(last)) and
          n2.isAfter(sw)
        )
      )
    }

    private predicate selectStmt(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::SelectStmt sel |
        n1.isBefore(sel) and
        (
          n2.isBefore(sel.getNonDefaultCommClause(0).getComm())
          or
          not exists(sel.getACommClause()) and n2.isAfter(sel)
        )
        or
        exists(Go::CommClause cc, int i | cc = sel.getNonDefaultCommClause(i) |
          n1.isAfter(cc.getComm()) and
          (
            n2.isBefore(sel.getNonDefaultCommClause(i + 1).getComm())
            or
            not exists(sel.getNonDefaultCommClause(i + 1)) and
            (
              n2.isBefore(sel.getACommClause().getStmt(0))
              or
              exists(sel.getDefaultCommClause()) and
              n2.isBefore(sel.getDefaultCommClause().getStmt(0))
            )
          )
        )
        or
        exists(Go::CommClause cc | sel.getACommClause() = cc |
          exists(int j | n1.isAfter(cc.getStmt(j)) and n2.isBefore(cc.getStmt(j + 1)))
          or
          exists(int last |
            last = max(int j | exists(cc.getStmt(j))) and
            n1.isAfter(cc.getStmt(last)) and
            n2.isAfter(sel)
          )
          or
          not exists(cc.getStmt(_)) and n1.isBefore(cc) and n2.isAfter(sel)
        )
      )
    }

    private predicate deferStmt(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::DeferStmt s |
        n1.isBefore(s) and n2.isBefore(s.getCall())
        or
        n1.isAfter(s.getCall()) and n2.isIn(s)
        or
        n1.isIn(s) and n2.isAfter(s)
      )
    }

    private predicate goStmtStep(PreControlFlowNode n1, PreControlFlowNode n2) {
      exists(Go::GoStmt s |
        n1.isBefore(s) and n2.isBefore(s.getCall())
        or
        n1.isAfter(s.getCall()) and n2.isIn(s)
        or
        n1.isIn(s) and n2.isAfter(s)
      )
    }
  }
}
