import faulthandler, os, subprocess, tempfile, sys
faulthandler.enable()
sys.path.insert(0, ".")
from leotower import Repl

# Mimic the test-suite context: several Repls importing Lean, dropped.
for i in range(6):
    r = Repl()
    r.set_goal("1 + 1 = 2")
    r.run_tac(0, "rfl")
    del r
    print(f"Lean Repl {i} created + dropped")

# Now the dotted-module import (like test_repl_imports_dotted_modules).
lean = os.environ.get("LEAN_BIN", "/home/ljm/.lemma/toolchains/v4.25.2-linux/bin/lean")
tmp = tempfile.mkdtemp()
src_dir = os.path.join(tmp, "basic")
os.makedirs(src_dir)
with open(os.path.join(src_dir, "MyThm.lean"), "w") as f:
    f.write("theorem my_thm : 1 + 1 = 2 := by rfl\n")
lib = os.path.join(tmp, "build", "lib", "lean", "basic")
os.makedirs(lib)
subprocess.run(
    [lean, "-R", tmp, "-o", os.path.join(lib, "MyThm.olean"),
     os.path.join(src_dir, "MyThm.lean")],
    check=True, capture_output=True,
)
os.environ["LEAN_PATH"] = os.path.join(tmp, "build", "lib", "lean")
print("creating Repl(basic.MyThm) after Lean Repls")
repl = Repl("basic.MyThm")
print("created; env_has_const:", repl.env_has_const("my_thm"))
print("dropping repl")
del repl
print("after del - no crash")
os._exit(0)