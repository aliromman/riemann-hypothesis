module

public import Init

-- clump member: Examples.Wrong
example : False := True.intro

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Examples.Leaf, Examples.Main

@[expose] public section -- clump member: Examples.Leaf
theorem leaf : False := True.intro
end -- clump:auto

@[expose] public section -- clump member: Examples.Main
theorem ordinary : True := True.intro

-- clump-header: {"m": "Examples.Leaf", "h": "module\npublic import Init\n\n"}
-- clump-header: {"m": "Examples.Main", "h": "module\npublic import Examples.Leaf\n\n"}
