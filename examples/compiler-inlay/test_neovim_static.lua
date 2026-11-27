-- Start a clean Neovim; FATOU_BIN points to the candidate executable.
-- A stock LSP attach with inlay hints enabled is the whole setup.
local dir = vim.fn.tempname() .. ' automatic inlay'
vim.fn.mkdir(dir, 'p')
local file = vim.fs.joinpath(dir, 'initializer.jl')
vim.fn.writefile({
  'function run(u)',
  '    linewidth = 200.0e6',
  '    Kappa_normal = 1',
  '    noise_amp = Vector{Float64}(undef, length(u))',
  '    noise_phase = similar(noise_amp)',
  '    changes = 1',
  '    changes += 2',
  '    for _ in u',
  '        in_loop = 2.0',
  '    end',
  '    return linewidth, Kappa_normal, noise_phase, changes',
  'end',
  'function construct(Vector, u)',
  '    custom = Vector{Float64}(undef, length(u))',
  '    return custom',
  'end',
}, file)
vim.cmd.edit(vim.fn.fnameescape(file))
local buf = vim.api.nvim_get_current_buf()
assert(vim.lsp.start({name = 'fatou', cmd = {assert(vim.env.FATOU_BIN), '--no-config', 'lsp'},
  root_dir = dir, on_attach = function(_, b) vim.lsp.inlay_hint.enable(true, {bufnr = b}) end}, {bufnr = buf}))
local function get() return vim.lsp.inlay_hint.get({bufnr = buf}) end
assert(vim.wait(16000, function() return #get() == 3 end, 20), vim.inspect(get()))
local expected = {[1] = '::Float64', [2] = '::Int', [3] = '::Vector{Float64}'}
for _, item in ipairs(get()) do
  local h = item.inlay_hint
  assert(expected[h.position.line] == h.label, vim.inspect(h))
  assert(h.tooltip:find('not a Julia compiler inference result', 1, true), vim.inspect(h))
  expected[h.position.line] = nil
end
assert(next(expected) == nil)
print('automatic ordinary LSP hints: Float64, Int, Vector{Float64}; omitted unknown, shadowed and mutated bindings')
vim.api.nvim_create_autocmd('VimLeavePre', {callback = function() vim.fn.delete(dir, 'rf') end})
vim.cmd('qa!')
