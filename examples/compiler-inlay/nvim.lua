-- Explicit session-only example for Neovim 0.11+. Load this script yourself;
-- it does not attach to buffers, modify your configuration, or run Julia.
local MAX_ARTIFACT = 8 * 1024 * 1024

local function client_for(buf)
  local clients = vim.lsp.get_clients({ bufnr = buf, name = 'fatou' })
  if #clients ~= 1 then
    vim.notify('Expected exactly one Fatou client in the current buffer', vim.log.levels.ERROR)
    return nil
  end
  return clients[1]
end

vim.api.nvim_create_user_command('FatouCompilerHintsImport', function(opts)
  local buf = vim.api.nvim_get_current_buf()
  local client = client_for(buf)
  if not client then return end
  local stream, failure = io.open(vim.fn.expand(opts.args), 'rb')
  if not stream then vim.notify(tostring(failure), vim.log.levels.ERROR); return end
  local data = stream:read(MAX_ARTIFACT + 1)
  stream:close()
  if not data or #data > MAX_ARTIFACT then
    vim.notify('Compiler hint report empty or larger than 8 MiB', vim.log.levels.ERROR)
    return
  end
  local ok, report = pcall(vim.json.decode, data)
  if not ok or type(report) ~= 'table' then
    vim.notify('Invalid JSON compiler hint report', vim.log.levels.ERROR)
    return
  end
  local uri = vim.uri_from_bufnr(buf)
  client:request('fatou/compilerHintsTarget', { uri = uri }, function(err, target)
    if err or not target then vim.notify(err and err.message or 'Missing compiler hints ticket', vim.log.levels.ERROR); return end
    client:request('fatou/compilerHintsImport', {
      uri = uri, version = target.version, ticket = target.ticket, snapshot = report,
    }, function(import_err, response)
      if import_err or not response then
        vim.notify(import_err and import_err.message or 'No compiler report was imported', vim.log.levels.ERROR)
        return
      end
      -- Display the successful explicit import now, on this buffer only.
      if vim.api.nvim_buf_is_valid(buf) then vim.lsp.inlay_hint.enable(true, { bufnr = buf }) end
      vim.notify(('Imported %d compiler type hints'):format(response.imported))
    end, buf)
  end, buf)
end, { nargs = 1, complete = 'file' })

vim.api.nvim_create_user_command('FatouCompilerHintsClear', function()
  local buf = vim.api.nvim_get_current_buf()
  local client = client_for(buf)
  if client then
    client:request('fatou/compilerHintsClear', {}, function(err)
      if err then vim.notify(err.message, vim.log.levels.ERROR) end
    end, buf)
  end
end, {})
