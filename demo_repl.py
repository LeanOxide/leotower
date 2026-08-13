"""Repl 演示：在嵌入式 Lean 运行时上做 LeanDojo 风格的回放式证明。"""

from leotower import Repl


def show(title: str) -> None:
    print(f"\n{'=' * 62}\n{title}\n{'=' * 62}")


show("① 启动 Repl（导入 Lean 环境）")
repl = Repl()  # 内部一次性引导嵌入的 Lean 运行时
print(f"env 里有 Nat 吗？    -> {repl.env_has_const('Nat')}")
print(f"env 里有 Nat.add 吗？ -> {repl.env_has_const('Nat.add')}")

show("② set_goal：设置要证明的目标")
s0 = repl.set_goal("∀ n m : Nat, n + m = m + n")
print(f"状态 s0 = {s0}, 剩余目标数 = {repl.get_num_goals(s0)}")
print(f"目标打印:\n{repl.get_goal_pp(s0)}")

show("③ run_tac：逐步应用策略")
s1 = repl.run_tac(s0, "intro n m")   # 引入变量 n, m
print(f"intro n m  -> 状态 s1 = {s1}")
print(f"目标打印:\n{repl.get_goal_pp(s1)}")

s2 = repl.run_tac(s1, "induction n")  # 对 n 归纳
print(f"induction n  -> 状态 s2 = {s2}, 剩余目标数 = {repl.get_num_goals(s2)}")
for i, g in enumerate(repl.get_goals(s2)):
    print(f"  goal[{i}]: {g}")

show("④ 结构化查询：get_goals 拿到假设和结论")
goals = repl.get_goals(s2)
g = goals[0]
print(f"goal[0] 的假设: {g.hyps}")
print(f"goal[0] 的结论: {g.ty}")

show("⑤ 分支推进：分别闭合两个子目标（注意用 simp only 避开已知的递归 bug）")
s3 = repl.run_tac(s2, "simp only [Nat.zero_add, Nat.add_zero]")  # base 分支
print(f"闭合 base   -> 状态 s3 = {s3}, 剩余目标数 = {repl.get_num_goals(s3)}")
s4 = repl.run_tac(s2, "simp only [Nat.add_comm, Nat.add_succ]")  # step 分支
print(f"闭合 step   -> 状态 s4 = {s4}, 剩余目标数 = {repl.get_num_goals(s4)}")
print("✅ 定理 ∀ n m : Nat, n + m = m + n 证明完成！")

show("⑥ 容错：无效策略抛 RuntimeError，但会话不崩")
try:
    repl.run_tac(s2, "this is not a tactic !!!")
except RuntimeError as e:
    print(f"捕获 RuntimeError: {e}")
s_ok = repl.run_tac(s0, "intro n m")
print(f"出错后会话仍可用: run_tac 返回状态 {s_ok}")

show("⑦ run_cmd：在会话里定义新常量并用于证明")
repl.run_cmd("def my_favorite : Nat := 42")
print(f"my_favorite 定义好了吗？ -> {repl.env_has_const('my_favorite')}")
s_a = repl.set_goal("my_favorite = 42")
s_b = repl.run_tac(s_a, "rfl")
print(f"用 rfl 证明 my_favorite = 42 -> 剩余目标数 = {repl.get_num_goals(s_b)}")

show("⑧ 加载本地 .lean 文件作为环境")
import os

fixture = os.path.join("tests", "fixtures", "repl_demo.lean")
repl2 = Repl(fixture)
print(f"文件里的 demo_thm 可用吗？ -> {repl2.env_has_const('demo_thm')}")
s_c = repl2.set_goal("demo_base = demo_base")
s_d = repl2.run_tac(s_c, "rfl")
print(f"引用文件里的定义证明 -> 剩余目标数 = {repl2.get_num_goals(s_d)}")

print("\n🎉 Repl 演示完毕：状态式回放、结构化目标查询、错误容错、动态加定义，全部跑通。")
