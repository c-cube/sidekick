#!/usr/bin/env lua

header = [[
(set-logic QF_UFDT)
(declare-datatypes ((t 0))
  (((T0) (T1 (prev1 t)) (T2 (prev2 t)))))
]]

footer = [[
(check-sat)
(exit)
]]

function printf(...)
  print(string.format(...))
end

function mkdiamond(n)
  -- decls
  for i=1,n do
    printf("(declare-const c%d t)", i)
  end
  printf("(assert (= c1 c%d))", n)

  -- now for the diamond itself
  for i=1,n do
    printf("(assert (not (= c%d T0)))",i)
  end
  for i=1, n-1 do
    local s = "c" .. i
    local next_ = "c" .. (i+1)

    printf("(assert (or (= %s (T1 %s)) (= %s (T2 %s))))", s, next_, s, next_)
  end
end

n = tonumber(arg[1])

print(header)
mkdiamond(n)
print(footer)
