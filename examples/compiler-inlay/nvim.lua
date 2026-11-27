-- Explicit session-only Neovim 0.11+ integration. Merely sourcing this file
-- does not execute Julia, attach a client, or change Neovim configuration.
local MAX_ARTIFACT = 8 * 1024 * 1024
local bundled_driver = vim.fs.joinpath(vim.fs.dirname(debug.getinfo(1, 'S').source:sub(2)), 'watch-function.jl')
local watches = {}
local watch_group = vim.api.nvim_create_augroup('FatouCompilerHintsWatch', { clear = true })

local function notify(message, level)
  if #message > 1500 then message = message:sub(1, 1500) .. '…' end
  vim.notify(message, level)
end

local function client_for(buf)
  local clients = vim.lsp.get_clients({ bufnr = buf, name = 'fatou' })
  if #clients ~= 1 then
    notify('Expected exactly one Fatou client in the current buffer', vim.log.levels.ERROR)
    return nil
  end
  return clients[1]
end

local function report_to_buffer(buf, client, data, current)
  if not current() then return end
  if not data or #data > MAX_ARTIFACT then
    notify('Compiler hint report empty or larger than 8 MiB', vim.log.levels.ERROR)
    return
  end
  local ok, report = pcall(vim.json.decode, data)
  if not ok or type(report) ~= 'table' then
    notify('Invalid JSON compiler hint report', vim.log.levels.ERROR)
    return
  end
  local uri = vim.uri_from_bufnr(buf)
  client:request('fatou/compilerHintsTarget', { uri = uri }, function(err, target)
    if not current() then return end
    if err or not target then
      notify(err and err.message or 'Missing compiler hints ticket', vim.log.levels.ERROR)
      return
    end
    client:request('fatou/compilerHintsImport', {
      uri = uri, version = target.version, ticket = target.ticket, snapshot = report,
    }, function(import_err, response)
      if not current() then return end
      if import_err or not response then
        notify(import_err and import_err.message or 'No compiler report was imported', vim.log.levels.ERROR)
        return
      end
      vim.lsp.inlay_hint.enable(true, { bufnr = buf })
      notify(('Imported %d compiler type hints'):format(response.imported))
    end, buf)
  end, buf)
end

vim.api.nvim_create_user_command('FatouCompilerHintsImport', function(opts)
  local buf = vim.api.nvim_get_current_buf()
  local client = client_for(buf)
  if not client then return end
  local stream, failure = io.open(vim.fn.expand(opts.args), 'rb')
  if not stream then notify(tostring(failure), vim.log.levels.ERROR); return end
  local data = stream:read(MAX_ARTIFACT + 1)
  stream:close()
  local tick = vim.api.nvim_buf_get_changedtick(buf)
  report_to_buffer(buf, client, data, function()
    return vim.api.nvim_buf_is_valid(buf) and vim.api.nvim_buf_get_changedtick(buf) == tick
  end)
end, { nargs = 1, complete = 'file' })

local function stop_watch(buf)
  local state = watches[buf]
  if not state then return end
  watches[buf] = nil
  if state.job then pcall(state.job.kill, state.job, 15) end
  for _, id in ipairs(state.autocmds) do pcall(vim.api.nvim_del_autocmd, id) end
end

local function run_watch(buf, state)
  if not vim.api.nvim_buf_is_valid(buf) or vim.bo[buf].modified then return end
  local client = client_for(buf)
  if not client or client.id ~= state.client then stop_watch(buf); return end
  local target = vim.api.nvim_buf_get_name(buf)
  local tick = vim.api.nvim_buf_get_changedtick(buf)
  local generation = state.generation + 1
  state.generation = generation
  if state.job then pcall(state.job.kill, state.job, 15) end
  local function current()
    return watches[buf] == state and state.generation == generation
      and vim.api.nvim_buf_is_valid(buf) and not vim.bo[buf].modified
      and vim.api.nvim_buf_get_changedtick(buf) == tick and vim.api.nvim_buf_get_name(buf) == target
  end
  local argv = { state.julia, '--startup-file=no', '--history-file=no', '--threads=1',
    '--project=' .. state.project, state.driver, target }
  if state.function_name then
    vim.list_extend(argv, {state.function_name, state.signature})
  end
  local ok, job = pcall(vim.system, argv, { cwd = state.project, timeout = 120000 }, function(result)
    vim.schedule(function()
      if watches[buf] ~= state or state.generation ~= generation then return end
      state.job = nil
      if not current() then return end
      if result.code ~= 0 then
        notify(('Compiler hint driver exited %s: %s'):format(result.code, result.stderr or ''), vim.log.levels.ERROR)
        return
      end
      report_to_buffer(buf, client, result.stdout, current)
    end)
  end)
  if not ok then notify(tostring(job), vim.log.levels.ERROR); return end
  state.job = job
end

vim.api.nvim_create_user_command('FatouCompilerHintsWatch', function(opts)
  local buf = vim.api.nvim_get_current_buf()
  local client = client_for(buf)
  if not client then return end
  local target = vim.api.nvim_buf_get_name(buf)
  if target == '' or vim.bo[buf].modified then
    notify('Save the Julia buffer before starting compiler hints', vim.log.levels.ERROR)
    return
  end
  local driver = vim.uv.fs_realpath(opts.args == '' and bundled_driver or vim.fn.expand(opts.args))
  local julia = vim.fn.exepath('julia')
  if not driver or not vim.uv.fs_stat(driver) or vim.uv.fs_stat(driver).type ~= 'file' or julia == '' then
    notify('Compiler hints need an existing trusted driver and julia on PATH', vim.log.levels.ERROR)
    return
  end
  local found = vim.fs.find({ 'JuliaProject.toml', 'Project.toml' }, {
    path = vim.fs.dirname(target), upward = true, type = 'file',
  })[1]
  local project = found and vim.fs.dirname(found) or vim.fs.dirname(target)
  local function_name, signature
  if opts.args == '' then
    function_name = vim.fn.input('Julia function (e.g. MyModule.solve): ')
    if function_name == '' then return end
    signature = vim.fn.input('Concrete Julia argument tuple: ', 'Tuple{}')
    if signature == '' then return end
  end
  local action = function_name and ('Load this saved Julia file now and on every save of this buffer?\n' .. target)
    or ('Execute this trusted Julia driver now and on every save of this buffer?\n' .. driver)
  local confirmed = vim.fn.confirm(
    action,
    '&No\n&Yes', 1
  )
  if confirmed ~= 2 then return end
  -- One compiler snapshot per server. A newly authorized watch replaces
  -- any previous watch on that same Fatou client.
  for watched, previous in pairs(watches) do
    if previous.client == client.id then stop_watch(watched) end
  end
  local state = { julia = julia, project = project, driver = driver, client = client.id,
    function_name = function_name, signature = signature, generation = 0, autocmds = {} }
  watches[buf] = state
  state.autocmds[1] = vim.api.nvim_create_autocmd('BufWritePost', {
    group = watch_group, buffer = buf, callback = function() run_watch(buf, state) end,
  })
  state.autocmds[2] = vim.api.nvim_create_autocmd({ 'BufWipeout', 'BufFilePost', 'LspDetach' }, {
    group = watch_group, buffer = buf, callback = function(evt)
      if evt.event ~= 'LspDetach' or evt.data.client_id == state.client then stop_watch(buf) end
    end,
  })
  run_watch(buf, state)
end, { nargs = '?', complete = 'file' })

vim.api.nvim_create_user_command('FatouCompilerHintsClear', function()
  local buf = vim.api.nvim_get_current_buf()
  stop_watch(buf)
  local client = client_for(buf)
  if client then
    client:request('fatou/compilerHintsClear', {}, function(err)
      if err then notify(err.message, vim.log.levels.ERROR) end
    end, buf)
  end
end, {})
