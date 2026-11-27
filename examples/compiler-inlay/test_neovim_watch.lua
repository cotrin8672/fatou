-- Invoke in a clean Neovim with FATOU_BIN and Julia 1.13.4 on PATH.
-- Copy into a scratch directory before intentionally changing the fixture.
local source = vim.fn.fnamemodify(debug.getinfo(1,'S').source:sub(2), ':h')
local dir = vim.fn.tempname() .. ' compiler hints'
vim.fn.mkdir(dir, 'p')
for _, name in ipairs({'bridge.jl', 'nvim.lua', 'fixture.jl', 'watch-demo.jl', 'watch-function.jl'}) do
  assert(vim.uv.fs_copyfile(source .. '/' .. name, dir .. '/' .. name))
end
vim.api.nvim_create_autocmd('VimLeavePre', {
  callback = function() vim.fn.delete(dir, 'rf') end,
})
local fatou = assert(vim.env.FATOU_BIN)
vim.cmd.edit(vim.fn.fnameescape(dir .. '/fixture.jl'))
local buf = vim.api.nvim_get_current_buf()
local id = assert(vim.lsp.start({name='fatou', cmd={fatou,'--no-config','lsp'}, root_dir=dir}, {bufnr=buf}))
assert(vim.wait(10000, function() local c=vim.lsp.get_client_by_id(id); return c and c.initialized end,20))
vim.cmd.luafile(vim.fn.fnameescape(dir .. '/nvim.lua'))
assert(#vim.lsp.inlay_hint.get({bufnr=buf})==0)
local count_confirm = 0
vim.fn.confirm = function(prompt, options, default)
  assert(prompt:find('every save',1,true) and options=='&No\n&Yes' and default==1)
  count_confirm=count_confirm+1
  return count_confirm == 1 and 1 or 2
end
local function watch()
  vim.cmd.FatouCompilerHintsWatch(vim.fn.fnameescape(dir..'/watch-demo.jl'))
end
watch()
assert(#vim.lsp.inlay_hint.get({bufnr=buf})==0)
vim.fn.input = function(prompt, default)
  if prompt:find('function', 1, true) then return 'callers' end
  assert(default == 'Tuple{}')
  return default
end
vim.cmd.FatouCompilerHintsWatch()
local function await(label)
  assert(vim.wait(40000,function()
    local hs = vim.lsp.inlay_hint.get({bufnr=buf})
    if #hs ~= 5 then return false end
    for _,h in ipairs(hs) do
      if h.inlay_hint.position.line == 11 and h.inlay_hint.label == label then
        return true
      end
    end
    return false
  end,20), vim.inspect(vim.lsp.inlay_hint.get({bufnr=buf})))
end
await('::Int64')
print('automatic initial inlay hints: 5, including ::Int64')
vim.api.nvim_buf_set_lines(buf,11,12,false,{'    a = scaled(2.0)'})
vim.bo[buf].fileformat = 'dos'
vim.cmd.write()
await('::Float64')
assert(count_confirm == 2)
print('save-triggered compiler re-inferred Int64 -> Float64 without JSON handoff or new authorization')
vim.cmd.FatouCompilerHintsClear()
assert(vim.wait(40000,function() return #vim.lsp.inlay_hint.get({bufnr=buf})==0 end,20))
print('clear removed automatic hints')
vim.cmd('qa!')
