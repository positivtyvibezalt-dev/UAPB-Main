--!nonstrict
--[[
	NewUAPB.lua — universal auto-parry / auto-dodge builder for any Roblox game.

	Run directly in an executor:
		loadstring(game:HttpGet("<url to NewUAPB.lua>"))()
	or place the file in the executor workspace folder and:
		loadstring(readfile("NewUAPB.lua"))()

	Storage layout (inside the executor workspace folder):
		UAPB/Timings/<name>.json            saved timing files
		UAPB/Configs/settings/*.json        Linoria SaveManager UI configs
		UAPB/Games/<PlaceId>.json           per-game data (remote templates, blacklist, autoload timing name)
		UAPB/Logs/difference_<PlaceId>_<time>.json exported difference samples
]]

--------------------------------------------------------------------------------
-- Services + executor shims
--------------------------------------------------------------------------------

-- Roblox engine builtins (game, workspace, Instance, Vector3, Vector2, CFrame, Color3, Enum,
-- task, warn, typeof, bit32, OverlapParams, loadstring, unpack) are used as plain globals.
local loadstringFn = loadstring
local unpackFn = unpack or table.unpack

-- Executor-provided environment accessors, read as plain globals.
local getgenvFn = getgenv
local getfenvFn = getfenv

---Resolve an executor-provided function: getgenv() first, then getfenv(0), then _G.
---@param name string
---@return any
local function env(name)
	if getgenvFn then
		local ok, envTable = pcall(getgenvFn)

		if ok and type(envTable) == "table" then
			local value = rawget(envTable, name)

			if value ~= nil then
				return value
			end
		end
	end

	if getfenvFn then
		local ok, fenv = pcall(getfenvFn, 0)

		if ok and type(fenv) == "table" then
			local value = rawget(fenv, name)

			if value ~= nil then
				return value
			end
		end
	end

	return rawget(_G, name)
end

local getgc = env("getgc")
local getrawmetatable = env("getrawmetatable")
local identifyexecutor = env("identifyexecutor")
local gethui = env("gethui")
local setclipboard = env("setclipboard") or env("toclipboard")

-- Linoria UI tables, assigned after the library loads.
local Toggles
local Options

local getgenvSafe = getgenvFn or function()
	return _G
end

local players = game:GetService("Players")
local runService = game:GetService("RunService")
local userInputService = game:GetService("UserInputService")
local httpService = game:GetService("HttpService")
local replicatedStorage = game:GetService("ReplicatedStorage")
local stats = game:GetService("Stats")
local virtualInputManager = game:GetService("VirtualInputManager")
local debris = game:GetService("Debris")
local localPlayer = players.LocalPlayer

-- Filesystem executor functions.
local isfolder = env("isfolder")
local makefolder = env("makefolder")
local isfile = env("isfile")
local readfile = env("readfile")
local writefile = env("writefile")
local listfiles = env("listfiles")
local delfile = env("delfile")

local FS_AVAILABLE = isfolder and makefolder and isfile and readfile and writefile and listfiles and delfile

if not FS_AVAILABLE then
	warn("[UAPB] Filesystem functions are unavailable on this executor. Saving/loading is disabled.")
end

-- Single-instance guard.
do
	local existing = getgenvSafe().UAPB

	if existing and type(existing) == "table" and type(existing.unload) == "function" then
		pcall(existing.unload)
	end
end

local UNLOADED = false

--------------------------------------------------------------------------------
-- SHA-256 (used by RemoteResolver's getgc fallback)
--------------------------------------------------------------------------------

local SHA256_K = {
	0x428a2f98,
	0x71374491,
	0xb5c0fbcf,
	0xe9b5dba5,
	0x3956c25b,
	0x59f111f1,
	0x923f82a4,
	0xab1c5ed5,
	0xd807aa98,
	0x12835b01,
	0x243185be,
	0x550c7dc3,
	0x72be5d74,
	0x80deb1fe,
	0x9bdc06a7,
	0xc19bf174,
	0xe49b69c1,
	0xefbe4786,
	0x0fc19dc6,
	0x240ca1cc,
	0x2de92c6f,
	0x4a7484aa,
	0x5cb0a9dc,
	0x76f988da,
	0x983e5152,
	0xa831c66d,
	0xb00327c8,
	0xbf597fc7,
	0xc6e00bf3,
	0xd5a79147,
	0x06ca6351,
	0x14292967,
	0x27b70a85,
	0x2e1b2138,
	0x4d2c6dfc,
	0x53380d13,
	0x650a7354,
	0x766a0abb,
	0x81c2c92e,
	0x92722c85,
	0xa2bfe8a1,
	0xa81a664b,
	0xc24b8b70,
	0xc76c51a3,
	0xd192e819,
	0xd6990624,
	0xf40e3585,
	0x106aa070,
	0x19a4c116,
	0x1e376c08,
	0x2748774c,
	0x34b0bcb5,
	0x391c0cb3,
	0x4ed8aa4a,
	0x5b9cca4f,
	0x682e6ff3,
	0x748f82ee,
	0x78a5636f,
	0x84c87814,
	0x8cc70208,
	0x90befffa,
	0xa4506ceb,
	0xbef9a3f7,
	0xc67178f2,
}

---@param num number
---@param iter number
---@return string
local function sha256Nts(num, iter)
	local str = ""

	for _ = 1, iter do
		local b = num % 256
		str = string.char(b) .. str
		num = (num - b) / 256
	end

	return str
end

---@param str string
---@param idx number
---@return number
local function sha256Stn(str, idx)
	local num = 0

	for i = idx, idx + 3 do
		num = num * 256 + string.byte(str, i)
	end

	return num
end

---@param msg string
---@param len number
---@return string
local function sha256Preprocess(msg, len)
	return msg .. string.char(128) .. string.rep(string.char(0), 64 - (len + 9) % 64) .. sha256Nts(8 * len, 8)
end

---@param msg string
---@param i number
---@param H table
local function sha256Digest(msg, i, H)
	local chunks = {}

	for j = 1, 16 do
		chunks[j] = sha256Stn(msg, i + (j - 1) * 4)
	end

	for j = 17, 64 do
		local a = chunks[j - 15]
		local s0 = bit32.bxor(bit32.rrotate(a, 7), bit32.rrotate(a, 18), bit32.rshift(a, 3))
		a = chunks[j - 2]
		chunks[j] = chunks[j - 16]
			+ s0
			+ chunks[j - 7]
			+ bit32.bxor(bit32.rrotate(a, 17), bit32.rrotate(a, 19), bit32.rshift(a, 10))
	end

	local a = H[1]
	local b = H[2]
	local c = H[3]
	local d = H[4]
	local e = H[5]
	local f = H[6]
	local g = H[7]
	local h = H[8]

	for iter = 1, 64 do
		local sumA = bit32.bxor(bit32.rrotate(a, 2), bit32.rrotate(a, 13), bit32.rrotate(a, 22))
		local maj = bit32.bxor(bit32.band(a, b), bit32.band(a, c), bit32.band(b, c))
		local sumE = bit32.bxor(bit32.rrotate(e, 6), bit32.rrotate(e, 11), bit32.rrotate(e, 25))
		local ch = bit32.bxor(bit32.band(e, f), bit32.band(bit32.bnot(e), g))
		local t1 = h + sumE + ch + SHA256_K[iter] + chunks[iter]
		local t2 = sumA + maj
		local newE = d + t1

		h = g
		g = f
		f = e
		e = newE
		d = c
		c = b
		b = a
		a = t1 + t2
	end

	H[1] = bit32.band(H[1] + a)
	H[2] = bit32.band(H[2] + b)
	H[3] = bit32.band(H[3] + c)
	H[4] = bit32.band(H[4] + d)
	H[5] = bit32.band(H[5] + e)
	H[6] = bit32.band(H[6] + f)
	H[7] = bit32.band(H[7] + g)
	H[8] = bit32.band(H[8] + h)
end

---@param message string
---@return string
local function sha256(message)
	if not bit32 then
		return message
	end

	local processed = sha256Preprocess(message, #message)

	local ht = {
		1779033703,
		3144134277,
		1013904242,
		2773480762,
		1359893119,
		2600822924,
		528734635,
		1541459225,
	}

	for iter = 1, #message, 64 do
		sha256Digest(processed, iter, ht)
	end

	return sha256Nts(ht[1], 4)
		.. sha256Nts(ht[2], 4)
		.. sha256Nts(ht[3], 4)
		.. sha256Nts(ht[4], 4)
		.. sha256Nts(ht[5], 4)
		.. sha256Nts(ht[6], 4)
		.. sha256Nts(ht[7], 4)
		.. sha256Nts(ht[8], 4)
end

--------------------------------------------------------------------------------
-- Logger
--------------------------------------------------------------------------------

local Library -- forward declaration, assigned in the UI section

local Logger = {}

---@param fmt string
---@return string
local function format(fmt, ...)
	local ok, result = pcall(string.format, tostring(fmt), ...)

	if ok then
		return result
	end

	return tostring(fmt)
end

---@param fmt string
---@return any
function Logger.notify(fmt, ...)
	local message = format(fmt, ...)

	if Library then
		Library:Notify(message)
	end

	print("[UAPB] " .. message)
	return message
end

---@param fmt string
---@return any
function Logger.longNotify(fmt, ...)
	local message = format(fmt, ...)

	if Library then
		Library:Notify(message, 7)
	end

	print("[UAPB] " .. message)
	return message
end

---@param fmt string
---@return any
function Logger.warn(fmt, ...)
	local message = format(fmt, ...)
	warn("[UAPB] " .. message)
	return message
end

---@param fmt string
---@return any
function Logger.info(fmt, ...)
	local message = format(fmt, ...)
	print("[UAPB] " .. message)
	return message
end

--------------------------------------------------------------------------------
-- Maid
--------------------------------------------------------------------------------

---@class Maid
---@field _data table
local Maid = {}
Maid.__index = Maid

---Mark a connection, function, instance, or another maid for cleanup.
---@param item any
---@return any
function Maid:mark(item)
	table.insert(self._data, item)
	return item
end

---Clean all marked items.
function Maid:clean()
	for _, item in next, self._data do
		local itemType = typeof(item)

		if itemType == "RBXScriptConnection" then
			item:Disconnect()
		elseif itemType == "function" then
			pcall(item)
		elseif itemType == "Instance" then
			item:Destroy()
		elseif itemType == "table" then
			if item.clean then
				item:clean()
			elseif item.disconnect then
				item:disconnect()
			elseif item.Disconnect then
				item:Disconnect()
			elseif item.Destroy then
				item:Destroy()
			end
		end
	end

	table.clear(self._data)
end

---@return Maid
function Maid.new()
	return setmetatable({ _data = {} }, Maid)
end

local rootMaid = Maid.new()

--------------------------------------------------------------------------------
-- Filesystem
--------------------------------------------------------------------------------

local ROOT_FOLDER = "UAPB"
local TIMINGS_FOLDER = "Timings" -- UAPB/Timings/<name>.json
local CONFIGS_FOLDER = "Configs" -- UAPB/Configs (Linoria SaveManager folder -> UAPB/Configs/settings/*.json)
local GAMES_FOLDER = "Games" -- UAPB/Games/<PlaceId>.json
local LOGS_FOLDER = "Logs" -- UAPB/Logs/animations_<PlaceId>.json

---@class Filesystem
---@field _path string
local Filesystem = {}
Filesystem.__index = Filesystem

---Create and get the current path.
---@return string
function Filesystem:path()
	if not isfolder(self._path) then
		makefolder(self._path)
	end

	return self._path
end

---Append path to current path.
---@param path string
---@return string
function Filesystem:append(path)
	return self:path() .. "/" .. path
end

---Check if filename is a file.
---@param filename string
---@return boolean
function Filesystem:file(filename)
	return isfile(self:append(filename))
end

---Read file from path.
---@param filename string
---@return string
function Filesystem:read(filename)
	if not self:file(filename) then
		return error("File does not exist or is a folder.", 2)
	end

	return readfile(self:append(filename))
end

---Write file to path.
---@param filename string
---@param contents string?
function Filesystem:write(filename, contents)
	writefile(self:append(filename), contents or "")
end

---Delete file from path.
---@param filename string
function Filesystem:delete(filename)
	if not self:file(filename) then
		return error("File does not exist or is a folder.", 2)
	end

	return delfile(self:append(filename))
end

---List bare file names, stripping the directory prefix regardless of separator.
---@return table
function Filesystem:list()
	local list = listfiles(self:path()) or {}
	local out = {}

	for _, path in next, list do
		local name = tostring(path):match("[^/\\]+$")

		if name then
			table.insert(out, name)
		end
	end

	return out
end

---@param sub string
---@return Filesystem?
function Filesystem.new(sub)
	if not FS_AVAILABLE then
		return nil
	end

	return setmetatable({ _path = ROOT_FOLDER .. "/" .. sub }, Filesystem)
end

--------------------------------------------------------------------------------
-- Timing model
--------------------------------------------------------------------------------

local ACTION_TYPES = { "Parry", "Dodge", "Jump", "Start Block", "End Block", "Custom Key", "Remote" }
local TIMING_TAGS = { "Undefined", "Critical", "Mantra", "M1" }

---Normalize an asset id into the "rbxassetid://<id>" form.
---@param value any
---@return string
local function normalizeAssetId(value)
	local str = tostring(value or "")
	local digits = str:match("%d+%s*$") or str:match("%d+")

	if not digits then
		return str
	end

	return "rbxassetid://" .. digits:gsub("%s", "")
end

---@class Action
---@field _type string
---@field _when number When the action will occur in milliseconds. Never access directly.
---@field name string
---@field hitbox Vector3
---@field ihbc boolean Ignore hitbox check.
---@field ping number?
---@field key string?
---@field remote string?
local Action = {}
Action.__index = Action

---Getter for when in seconds.
---@return number
function Action:when()
	return self._when / 1000
end

---Load from partial values.
---@param values table
function Action:load(values)
	if typeof(values._type) == "string" then
		self._type = values._type
	end

	if typeof(values._when) == "number" then
		self._when = values._when
	elseif typeof(values.when) == "number" then
		self._when = values.when
	end

	if typeof(values.name) == "string" then
		self.name = values.name
	end

	if typeof(values.hitbox) == "table" then
		self.hitbox = Vector3.new(values.hitbox.X or 0, values.hitbox.Y or 0, values.hitbox.Z or 0)
	end

	if typeof(values.ihbc) == "boolean" then
		self.ihbc = values.ihbc
	end

	if typeof(values.ping) == "number" then
		self.ping = values.ping
	end

	if typeof(values.key) == "string" then
		self.key = values.key
	end

	if typeof(values.remote) == "string" then
		self.remote = values.remote
	end
end

---Clone action.
---@return Action
function Action:clone()
	local clone = Action.new()

	clone._type = self._type
	clone._when = self._when
	clone.name = self.name
	clone.hitbox = self.hitbox
	clone.ihbc = self.ihbc
	clone.ping = self.ping
	clone.key = self.key
	clone.remote = self.remote

	return clone
end

---Return a serializable table.
---@return table
function Action:serialize()
	local data = {
		_type = self._type,
		_when = self._when,
		name = self.name,
		hitbox = {
			X = self.hitbox.X,
			Y = self.hitbox.Y,
			Z = self.hitbox.Z,
		},
		ihbc = self.ihbc,
	}

	if self.ping then
		data.ping = self.ping
	end

	if self.key then
		data.key = self.key
	end

	if self.remote then
		data.remote = self.remote
	end

	return data
end

---Deserialize a table into an Action.
---@param t table
---@return Action
function Action.deserialize(t)
	return Action.new(t)
end

---Create new Action object.
---@param values table?
---@return Action
function Action.new(values)
	local self = setmetatable({}, Action)

	self._type = "Parry"
	self._when = 0
	self.name = ""
	self.hitbox = Vector3.zero
	self.ihbc = false

	if values then
		self:load(values)
	end

	return self
end

---@class ActionContainer
---@field _data Action[] Array ordered by _when.
local ActionContainer = {}
ActionContainer.__index = ActionContainer

---Push an action to the list.
---@param action Action
---@return boolean, string?
function ActionContainer:push(action)
	if self:find(action.name) then
		return false, string.format("Action name '%s' already exists in container.", action.name)
	end

	table.insert(self._data, action)
	table.sort(self._data, function(a, b)
		return a._when < b._when
	end)

	return true
end

---Remove an action from the list.
---@param action Action
function ActionContainer:remove(action)
	local idx = table.find(self._data, action)

	if idx then
		table.remove(self._data, idx)
	end
end

---Find an action by name.
---@param name string
---@return Action?
function ActionContainer:find(name)
	for _, action in next, self._data do
		if action.name == name then
			return action
		end
	end

	return nil
end

---List all action names in order.
---@return string[]
function ActionContainer:names()
	local names = {}

	for _, action in next, self._data do
		table.insert(names, action.name)
	end

	return names
end

---Get actions sorted by _when.
---@return Action[]
function ActionContainer:sorted()
	local out = table.clone(self._data)

	table.sort(out, function(a, b)
		return a._when < b._when
	end)

	return out
end

---Get action count.
---@return number
function ActionContainer:count()
	return #self._data
end

---Clone action container.
---@return ActionContainer
function ActionContainer:clone()
	local clone = ActionContainer.new()

	for _, action in next, self._data do
		clone:push(action:clone())
	end

	return clone
end

---Load from serialized array.
---@param arr table
function ActionContainer:load(arr)
	for _, data in next, arr do
		self:push(Action.deserialize(data))
	end
end

---Return a serializable array.
---@return table
function ActionContainer:serialize()
	local data = {}

	for _, action in next, self:sorted() do
		table.insert(data, action:serialize())
	end

	return data
end

---Create new ActionContainer object.
---@param values table?
---@return ActionContainer
function ActionContainer.new(values)
	local self = setmetatable({}, ActionContainer)

	self._data = {}

	if values then
		self:load(values)
	end

	return self
end

---@class Timing
---@field name string
---@field tag string
---@field imdd number Initial minimum distance.
---@field imxd number Initial maximum distance.
---@field duih boolean Delay until in hitbox.
---@field punishable number
---@field after number
---@field actions ActionContainer
---@field hitbox Vector3
---@field fhb boolean Hitbox facing offset.
---@field hso number Hitbox shift offset.
---@field ndfb boolean No dodge fallback.
---@field nbfb boolean No block fallback.
---@field bfht number Block fallback hold time.
---@field rpue boolean Repeat until end.
---@field _rsd number Repeat start delay in milliseconds.
---@field _rpd number Repeat delay in milliseconds.
---@field srpn boolean Skip repeat notification.
local Timing = {}
Timing.__index = Timing

---Getter for repeat start delay in seconds.
---@return number
function Timing:rsd()
	return self._rsd / 1000
end

---Getter for repeat delay in seconds.
---@return number
function Timing:rpd()
	return self._rpd / 1000
end

---Timing ID. Override me.
---@return string
function Timing:id()
	return self.name
end

---Load from partial values.
---@param values table
function Timing:load(values)
	if typeof(values.name) == "string" then
		self.name = values.name
	end

	if typeof(values.tag) == "string" then
		self.tag = values.tag
	end

	if typeof(values.imdd) == "number" then
		self.imdd = values.imdd
	end

	if typeof(values.imxd) == "number" then
		self.imxd = values.imxd
	end

	if typeof(values.duih) == "boolean" then
		self.duih = values.duih
	end

	if typeof(values.punishable) == "number" then
		self.punishable = values.punishable
	end

	if typeof(values.after) == "number" then
		self.after = values.after
	end

	if typeof(values.actions) == "table" then
		self.actions:load(values.actions)
	end

	if typeof(values.hitbox) == "table" then
		self.hitbox = Vector3.new(values.hitbox.X or 0, values.hitbox.Y or 0, values.hitbox.Z or 0)
	end

	if typeof(values.fhb) == "boolean" then
		self.fhb = values.fhb
	end

	if typeof(values.hso) == "number" then
		self.hso = values.hso
	end

	if typeof(values.ndfb) == "boolean" then
		self.ndfb = values.ndfb
	end

	if typeof(values.nbfb) == "boolean" then
		self.nbfb = values.nbfb
	end

	if typeof(values.bfht) == "number" then
		self.bfht = values.bfht
	end

	if typeof(values.rpue) == "boolean" then
		self.rpue = values.rpue
	end

	if typeof(values._rsd) == "number" then
		self._rsd = values._rsd
	elseif typeof(values.rsd) == "number" then
		self._rsd = values.rsd
	end

	if typeof(values._rpd) == "number" then
		self._rpd = values._rpd
	elseif typeof(values.rpd) == "number" then
		self._rpd = values.rpd
	end

	if typeof(values.srpn) == "boolean" then
		self.srpn = values.srpn
	end
end

---Clone timing.
---@return Timing
function Timing:clone()
	local clone = Timing.new()

	clone.name = self.name
	clone.tag = self.tag
	clone.imdd = self.imdd
	clone.imxd = self.imxd
	clone.duih = self.duih
	clone.punishable = self.punishable
	clone.after = self.after
	clone.actions = self.actions:clone()
	clone.hitbox = self.hitbox
	clone.fhb = self.fhb
	clone.hso = self.hso
	clone.ndfb = self.ndfb
	clone.nbfb = self.nbfb
	clone.bfht = self.bfht
	clone.rpue = self.rpue
	clone._rsd = self._rsd
	clone._rpd = self._rpd
	clone.srpn = self.srpn

	return clone
end

---Return a serializable table.
---@return table
function Timing:serialize()
	return {
		name = self.name,
		tag = self.tag,
		imdd = self.imdd,
		imxd = self.imxd,
		duih = self.duih,
		punishable = self.punishable,
		after = self.after,
		actions = self.actions:serialize(),
		hitbox = {
			X = self.hitbox.X,
			Y = self.hitbox.Y,
			Z = self.hitbox.Z,
		},
		fhb = self.fhb,
		hso = self.hso,
		ndfb = self.ndfb,
		nbfb = self.nbfb,
		bfht = self.bfht,
		rpue = self.rpue,
		_rsd = self._rsd,
		_rpd = self._rpd,
		srpn = self.srpn,
	}
end

---Create new Timing object.
---@param values table?
---@return Timing
function Timing.new(values)
	local self = setmetatable({}, Timing)

	self.name = "N/A"
	self.tag = "Undefined"
	self.imdd = 0
	self.imxd = 1000
	self.duih = false
	self.punishable = 0.6
	self.after = 0.1
	self.actions = ActionContainer.new()
	self.hitbox = Vector3.zero
	self.fhb = true
	self.hso = 0
	self.ndfb = false
	self.nbfb = false
	self.bfht = 0.3
	self.rpue = false
	self._rsd = 0
	self._rpd = 0
	self.srpn = false

	if values then
		self:load(values)
	end

	return self
end

---@class AnimationTiming: Timing
---@field _id string
---@field ha boolean
---@field iae boolean Ignore animation end.
---@field ieae boolean Ignore early animation end.
---@field mat number Max animation timeout in milliseconds.
---@field phd boolean
---@field phds number
---@field pfh boolean
---@field pfht number
---@field dp boolean
local AnimationTiming = setmetatable({}, { __index = Timing })
AnimationTiming.__index = AnimationTiming

---@return string
function AnimationTiming:id()
	return self._id
end

---@param values table
function AnimationTiming:load(values)
	Timing.load(self, values)

	if typeof(values._id) == "string" then
		self._id = normalizeAssetId(values._id)
	end

	if typeof(values.ha) == "boolean" then
		self.ha = values.ha
	end

	if typeof(values.iae) == "boolean" then
		self.iae = values.iae
	end

	if typeof(values.ieae) == "boolean" then
		self.ieae = values.ieae
	end

	if typeof(values.mat) == "number" then
		self.mat = values.mat
	end

	if typeof(values.phd) == "boolean" then
		self.phd = values.phd
	end

	if typeof(values.phds) == "number" then
		self.phds = values.phds
	end

	if typeof(values.pfh) == "boolean" then
		self.pfh = values.pfh
	end

	if typeof(values.pfht) == "number" then
		self.pfht = values.pfht
	end

	if typeof(values.dp) == "boolean" then
		self.dp = values.dp
	end
end

---@return AnimationTiming
function AnimationTiming:clone()
	local clone = setmetatable(Timing.clone(self), AnimationTiming)

	clone._id = self._id
	clone.ha = self.ha
	clone.iae = self.iae
	clone.ieae = self.ieae
	clone.mat = self.mat
	clone.phd = self.phd
	clone.phds = self.phds
	clone.pfh = self.pfh
	clone.pfht = self.pfht
	clone.dp = self.dp

	return clone
end

---@return table
function AnimationTiming:serialize()
	local serializable = Timing.serialize(self)

	serializable._id = self._id
	serializable.ha = self.ha
	serializable.iae = self.iae
	serializable.ieae = self.ieae
	serializable.mat = self.mat
	serializable.phd = self.phd
	serializable.phds = self.phds
	serializable.pfh = self.pfh
	serializable.pfht = self.pfht
	serializable.dp = self.dp

	return serializable
end

---@param values table?
---@return AnimationTiming
function AnimationTiming.new(values)
	local self = setmetatable(Timing.new(), AnimationTiming)

	self._id = ""
	self.ha = false
	self.iae = false
	self.ieae = false
	self.mat = 2000
	self.phd = false
	self.phds = 0
	self.pfh = false
	self.pfht = 0.15
	self.dp = false

	if values then
		self:load(values)
	end

	return self
end

---@class SoundTiming: Timing
---@field _id string
local SoundTiming = setmetatable({}, { __index = Timing })
SoundTiming.__index = SoundTiming

---@return string
function SoundTiming:id()
	return self._id
end

---@param values table
function SoundTiming:load(values)
	Timing.load(self, values)

	if typeof(values._id) == "string" then
		self._id = normalizeAssetId(values._id)
	end
end

---@return SoundTiming
function SoundTiming:clone()
	local clone = setmetatable(Timing.clone(self), SoundTiming)

	clone._id = self._id

	return clone
end

---@return table
function SoundTiming:serialize()
	local serializable = Timing.serialize(self)

	serializable._id = self._id

	return serializable
end

---@param values table?
---@return SoundTiming
function SoundTiming.new(values)
	local self = setmetatable(Timing.new(), SoundTiming)

	self._id = ""

	if values then
		self:load(values)
	end

	return self
end

---@class PartTiming: Timing
---@field pname string
---@field pparent string
local PartTiming = setmetatable({}, { __index = Timing })
PartTiming.__index = PartTiming

---@return string
function PartTiming:id()
	return self.pname
end

---@param values table
function PartTiming:load(values)
	Timing.load(self, values)

	if typeof(values.pname) == "string" then
		self.pname = values.pname
	end

	if typeof(values.pparent) == "string" then
		self.pparent = values.pparent
	end
end

---@return PartTiming
function PartTiming:clone()
	local clone = setmetatable(Timing.clone(self), PartTiming)

	clone.pname = self.pname
	clone.pparent = self.pparent

	return clone
end

---@return table
function PartTiming:serialize()
	local serializable = Timing.serialize(self)

	serializable.pname = self.pname
	serializable.pparent = self.pparent

	return serializable
end

---@param values table?
---@return PartTiming
function PartTiming.new(values)
	local self = setmetatable(Timing.new(), PartTiming)

	self.pname = ""
	self.pparent = ""

	if values then
		self:load(values)
	end

	return self
end

---@class EffectTiming: Timing
---@field ename string
local EffectTiming = setmetatable({}, { __index = Timing })
EffectTiming.__index = EffectTiming

---@return string
function EffectTiming:id()
	return self.ename
end

---@param values table
function EffectTiming:load(values)
	Timing.load(self, values)

	if typeof(values.ename) == "string" then
		self.ename = values.ename
	end
end

---@return EffectTiming
function EffectTiming:clone()
	local clone = setmetatable(Timing.clone(self), EffectTiming)

	clone.ename = self.ename

	return clone
end

---@return table
function EffectTiming:serialize()
	local serializable = Timing.serialize(self)

	serializable.ename = self.ename

	return serializable
end

---@param values table?
---@return EffectTiming
function EffectTiming.new(values)
	local self = setmetatable(Timing.new(), EffectTiming)

	self.ename = ""

	if values then
		self:load(values)
	end

	return self
end

---@class TimingContainer
---@field timings table<string, Timing>
---@field module table
local TimingContainer = {}
TimingContainer.__index = TimingContainer

---Push a timing into the container.
---@param timing Timing
---@return boolean, string?
function TimingContainer:push(timing)
	local id = timing:id()

	if not id or #id == 0 then
		return false, "Timing must have a valid identifier."
	end

	if self.timings[id] then
		return false, string.format("Timing identifier '%s' already exists in container.", id)
	end

	if self:find(timing.name) then
		return false, string.format("Timing name '%s' already exists in container.", timing.name)
	end

	self.timings[id] = timing
	return true
end

---Remove a timing.
---@param timing Timing
function TimingContainer:remove(timing)
	local id = timing:id()

	if id and self.timings[id] == timing then
		self.timings[id] = nil
		return
	end

	for key, value in next, self.timings do
		if value == timing then
			self.timings[key] = nil
		end
	end
end

---Find a timing by name.
---@param name string
---@return Timing?
function TimingContainer:find(name)
	for _, timing in next, self.timings do
		if timing.name == name then
			return timing
		end
	end

	return nil
end

---Find a timing by id.
---@param id string
---@return Timing?
function TimingContainer:index(id)
	return self.timings[id]
end

---List timing names, sorted.
---@return string[]
function TimingContainer:names()
	local names = {}

	for _, timing in next, self.timings do
		table.insert(names, timing.name)
	end

	table.sort(names)
	return names
end

---Get timing count.
---@return number
function TimingContainer:count()
	local count = 0

	for _ in next, self.timings do
		count = count + 1
	end

	return count
end

---Return a serializable array.
---@return table
function TimingContainer:serialize()
	local out = {}

	for _, timing in next, self.timings do
		table.insert(out, timing:serialize())
	end

	return out
end

---Load from serialized array.
---@param arr table
function TimingContainer:load(arr)
	for _, data in next, arr do
		local timing = self.module.new(data)
		local ok, err = self:push(timing)

		if not ok then
			Logger.warn("Failed to load timing: %s", err)
		end
	end
end

---Clear all timings.
function TimingContainer:clear()
	self.timings = {}
end

---@param module table
---@return TimingContainer
function TimingContainer.new(module)
	local self = setmetatable({}, TimingContainer)

	self.timings = {}
	self.module = module

	return self
end

---@class TimingSave
---@field _data table<string, TimingContainer>
local TimingSave = {}
TimingSave.__index = TimingSave

local TIMING_SAVE_VERSION = 1

---Get timing containers.
---@return table<string, TimingContainer>
function TimingSave:get()
	return self._data
end

---Clear timing containers.
function TimingSave:clear()
	for _, container in next, self._data do
		container:clear()
	end
end

---Load from partial values.
---@param values table
function TimingSave:load(values)
	local data = self._data

	if typeof(values.animation) == "table" then
		data.animation:load(values.animation)
	end

	if typeof(values.effect) == "table" then
		data.effect:load(values.effect)
	end

	if typeof(values.part) == "table" then
		data.part:load(values.part)
	end

	if typeof(values.sound) == "table" then
		data.sound:load(values.sound)
	end
end

---Get timing save count.
---@return number
function TimingSave:count()
	local count = 0

	for _, container in next, self._data do
		count = count + container:count()
	end

	return count
end

---Return a serializable table.
---@return table
function TimingSave:serialize()
	local data = self._data

	return {
		version = TIMING_SAVE_VERSION,
		animation = data.animation:serialize(),
		effect = data.effect:serialize(),
		part = data.part:serialize(),
		sound = data.sound:serialize(),
	}
end

---Create new TimingSave object.
---@param values table?
---@return TimingSave
function TimingSave.new(values)
	local self = setmetatable({}, TimingSave)

	self._data = {
		animation = TimingContainer.new(AnimationTiming),
		effect = TimingContainer.new(EffectTiming),
		part = TimingContainer.new(PartTiming),
		sound = TimingContainer.new(SoundTiming),
	}

	if values then
		self:load(values)
	end

	return self
end

-- The single live TimingSave instance. The builder mutates timings in place inside it
-- and the defenders read from the same containers at execution time.
local config = TimingSave.new()

local TIMING_CLASSES = {
	animation = AnimationTiming,
	sound = SoundTiming,
	part = PartTiming,
	effect = EffectTiming,
}

--------------------------------------------------------------------------------
-- Storage
--------------------------------------------------------------------------------

local placeId = game.PlaceId

---@class GameData
---@field data table
---@field fs Filesystem?
local GameData = {
	data = {},
	fs = nil,
	loaded = false,
}

---@return string
function GameData.filename()
	return tostring(placeId) .. ".json"
end

---Load per-game data.
function GameData.load()
	GameData.data = {}
	GameData.loaded = true

	if not FS_AVAILABLE then
		return
	end

	GameData.fs = GameData.fs or Filesystem.new(GAMES_FOLDER)

	local ok, err = pcall(function()
		if GameData.fs:file(GameData.filename()) then
			local decoded = httpService:JSONDecode(GameData.fs:read(GameData.filename()))

			if typeof(decoded) == "table" then
				GameData.data = decoded
			end
		end
	end)

	if not ok then
		Logger.warn("Failed to load game data: %s", err)
	end

	GameData.data.remotes = GameData.data.remotes or {}
end

---Save per-game data.
function GameData.save()
	if not FS_AVAILABLE or not GameData.fs then
		return
	end

	local ok, err = pcall(function()
		GameData.fs:write(GameData.filename(), httpService:JSONEncode(GameData.data))
	end)

	if not ok then
		Logger.warn("Failed to save game data: %s", err)
	end
end

---@class TimingStore
local TimingStore = {
	fs = nil,
	current = nil, -- currently loaded file name (no extension)
	dirty = false,
	lastSave = 0,
}

---@return Filesystem?
local function timingsFs()
	if not FS_AVAILABLE then
		return nil
	end

	TimingStore.fs = TimingStore.fs or Filesystem.new(TIMINGS_FOLDER)
	return TimingStore.fs
end

---List saved timing names without the .json extension.
---@return string[]
function TimingStore.list()
	local fs = timingsFs()

	if not fs then
		return {}
	end

	local ok, files = pcall(function()
		return fs:list()
	end)

	if not ok then
		return {}
	end

	local names = {}

	for _, file in next, files do
		local name = file:gsub("%.json$", "")
		table.insert(names, name)
	end

	table.sort(names)
	return names
end

---Save the live config under a name.
---@param name string
function TimingStore.save(name)
	local fs = timingsFs()

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot save timings.")
	end

	local ok, err = pcall(function()
		fs:write(name .. ".json", httpService:JSONEncode(config:serialize()))
	end)

	if ok then
		TimingStore.dirty = false
		TimingStore.current = name
		TimingStore.lastSave = os.clock()
		Logger.notify("Saved timings to '%s'.", name)
	else
		Logger.warn("Failed to save timings: %s", err)
	end
end

---Create a new (empty) timing file. Fails if it already exists.
---@param name string
function TimingStore.create(name)
	local fs = timingsFs()

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot create timings.")
	end

	if fs:file(name .. ".json") then
		return Logger.warn("The timing file '%s' already exists.", name)
	end

	config:clear()

	local ok, err = pcall(function()
		fs:write(name .. ".json", httpService:JSONEncode(config:serialize()))
	end)

	if ok then
		TimingStore.dirty = false
		TimingStore.current = name
		TimingStore.lastSave = os.clock()
		Logger.notify("Created timing file '%s'.", name)
	else
		Logger.warn("Failed to create timing file: %s", err)
	end
end

---Load a timing file into the live config.
---@param name string
function TimingStore.load(name)
	local fs = timingsFs()

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot load timings.")
	end

	if not fs:file(name .. ".json") then
		return Logger.warn("The timing file '%s' does not exist.", name)
	end

	local ok, err = pcall(function()
		local decoded = httpService:JSONDecode(fs:read(name .. ".json"))

		config:clear()
		config:load(decoded)
	end)

	if ok then
		TimingStore.dirty = false
		TimingStore.current = name
		Logger.notify("Loaded timings from '%s' (%d timings).", name, config:count())
	else
		Logger.warn("Failed to load timings: %s", err)
	end
end

---Clear a timing file's contents.
---@param name string
function TimingStore.clear(name)
	local fs = timingsFs()

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot clear timings.")
	end

	if not fs:file(name .. ".json") then
		return Logger.warn("The timing file '%s' does not exist.", name)
	end

	local ok, err = pcall(function()
		fs:write(name .. ".json", httpService:JSONEncode(TimingSave.new():serialize()))
	end)

	if ok then
		if TimingStore.current == name then
			config:clear()
			TimingStore.dirty = false
		end

		Logger.notify("Cleared timing file '%s'.", name)
	else
		Logger.warn("Failed to clear timing file: %s", err)
	end
end

---Delete a timing file.
---@param name string
function TimingStore.delete(name)
	local fs = timingsFs()

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot delete timings.")
	end

	if not fs:file(name .. ".json") then
		return Logger.warn("The timing file '%s' does not exist.", name)
	end

	local ok, err = pcall(function()
		fs:delete(name .. ".json")
	end)

	if ok then
		if TimingStore.current == name then
			TimingStore.current = nil
		end

		Logger.notify("Deleted timing file '%s'.", name)
	else
		Logger.warn("Failed to delete timing file: %s", err)
	end
end

---Mark the live config as dirty. Call after any builder mutation.
function TimingStore.markDirty()
	TimingStore.dirty = true
end

---Write the per-game autoload record.
---@param name string?
function TimingStore.autoload(name)
	GameData.data.autoloadTimings = name
	GameData.save()
end

---Heartbeat autosave when dirty.
function TimingStore.heartbeat()
	if not TimingStore.dirty or not TimingStore.current then
		return
	end

	local enabled = Toggles and Toggles.PeriodicAutoSave and Toggles.PeriodicAutoSave.Value
	local interval = (Options and Options.PeriodicAutoSaveInterval and Options.PeriodicAutoSaveInterval.Value) or 15

	if not enabled then
		return
	end

	if os.clock() - TimingStore.lastSave < interval then
		return
	end

	TimingStore.save(TimingStore.current)
end

--------------------------------------------------------------------------------
-- RemoteResolver
--------------------------------------------------------------------------------

---@class RemoteTemplate
---@field path string
---@field method string "FireServer"|"InvokeServer"
---@field args table
---@field name string

local GameDataRemotes -- alias kept for readability: GameData.data.remotes
local GameDataRemotesDisabled -- GameData.data.remotesDisabled

---@class RemoteResolver
local RemoteResolver = {
	cache = {},
}

---Check whether an instance is a remote.
---@param inst any
---@return boolean
local function isRemote(inst)
	if typeof(inst) ~= "Instance" then
		return false
	end

	return inst:IsA("RemoteEvent") or inst:IsA("RemoteFunction") or inst:IsA("UnreliableRemoteEvent")
end

---Parse a Lua-style instance path into { root = Instance, segments = string[] }.
---Accepts: `game:GetService("X")`, `game.X`, `workspace`, `game.Workspace`, `Players.LocalPlayer`,
---bracket indexing `["Name with spaces"]`, and the literal token PLAYERNAME (-> localPlayer.Name).
---@param path string
---@return Instance?, string[]
local function parseInstancePath(path)
	local text = tostring(path or ""):gsub("PLAYERNAME", localPlayer and localPlayer.Name or "")
	text = text:gsub("^%s+", ""):gsub("%s+$", "")

	local segments = {}
	local root = nil
	local pos, len = 1, #text

	while pos <= len do
		local progressed = false
		local _, name, nextpos = text:match('^%s*[%a_][%w_]*%s*:%s*GetService%s*%(%s*"([^"]*)"%s*%)()', pos)

		if not name then
			_, name, nextpos = text:match("^%s*[%a_][%w_]*%s*:%s*GetService%s*%(%s*'([^']*)'%s*%)()", pos)
		end

		if not name then
			_, name, nextpos = text:match("^%s*[%a_][%w_]*%s*:%s*GetService%s*%(%s*%[%[(.-)%]%]%s*%)()", pos)
		end

		if name then
			local ok, svc = pcall(game.GetService, game, name)

			if ok then
				root = svc
			end

			pos = nextpos
			progressed = true
		else
			local segment = nil
			segment, nextpos = text:match('^%s*%[%s*"([^"]*)"%s*%]()', pos)

			if not segment then
				segment, nextpos = text:match("^%s*%[%s*'([^']*)'%s*%]()", pos)
			end

			if not segment then
				segment, nextpos = text:match("^%s*([%w_]+)()", pos)
			end

			if segment then
				table.insert(segments, segment)
				pos = nextpos
				progressed = true
			end
		end

		-- Consume a '.' separator (or any other stray delimiter).
		local sep = text:match("^%s*[%.:%(%)]*%s*()", pos)

		if sep and sep > pos then
			pos = sep
		elseif not progressed then
			pos = pos + 1
		end
	end

	if not root then
		local first = segments[1]

		if first == "game" then
			root = game
			table.remove(segments, 1)

			local ok, svc = pcall(game.GetService, game, segments[1] or "")

			if ok and svc then
				root = svc
				table.remove(segments, 1)
			end
		elseif first == "workspace" or first == "Workspace" then
			root = workspace
			table.remove(segments, 1)
		elseif first then
			local ok, svc = pcall(game.GetService, game, first)

			if ok and svc then
				root = svc
				table.remove(segments, 1)
			else
				root = game
			end
		end
	end

	-- `Players.LocalPlayer` resolves to the local player instance.
	if root == players and segments[1] == "LocalPlayer" then
		root = localPlayer
		table.remove(segments, 1)
	end

	return root, segments
end

---Walk a path from game, supporting names containing '.' via a last-segment descendant match.
---@param path string
---@return Instance?
local function walkPath(path)
	local root, segments = parseInstancePath(path)
	local current = root

	for _, segment in next, segments do
		current = current and current:FindFirstChild(segment)

		if not current then
			break
		end
	end

	if current then
		return current
	end

	-- Last-segment descendant match for names containing dots or non-direct paths.
	local last = segments[#segments]

	if not last then
		return nil
	end

	local ok, found = pcall(function()
		for _, inst in next, game:GetDescendants() do
			if inst.Name == last then
				return inst
			end
		end

		return nil
	end)

	return ok and found or nil
end

---Resolve a dotted path or remote name to an instance.
---@param pathOrName string
---@return Instance?
function RemoteResolver.resolve(pathOrName)
	if not pathOrName or #pathOrName == 0 then
		return nil
	end

	local _, nameSegments = parseInstancePath(pathOrName)
	local name = nameSegments[#nameSegments] or pathOrName

	if RemoteResolver.cache[pathOrName] then
		local cached = RemoteResolver.cache[pathOrName]

		if cached and cached.Parent then
			return cached
		end

		RemoteResolver.cache[pathOrName] = nil
	end

	-- 1. Walk the path.
	if pathOrName:find("[%s%.:%[%]]") then
		local inst = walkPath(pathOrName)

		if inst then
			RemoteResolver.cache[pathOrName] = inst
			return inst
		end
	end

	-- 2. Search common roots for a remote with that name.
	local roots = {
		replicatedStorage,
		workspace,
		localPlayer,
	}

	pcall(function()
		table.insert(roots, game:GetService("ReplicatedFirst"))
	end)

	for _, root in next, roots do
		if not root then
			continue
		end

		local ok, found = pcall(function()
			for _, inst in next, root:GetDescendants() do
				if inst.Name == name and isRemote(inst) then
					return inst
				end
			end

			return nil
		end)

		if ok and found then
			RemoteResolver.cache[pathOrName] = found
			return found
		end

		-- Direct child check for non-model roots.
		local child = root.FindFirstChild and root:FindFirstChild(name)

		if child and isRemote(child) then
			RemoteResolver.cache[pathOrName] = child
			return child
		end
	end

	-- 3. getgc fallback: scan garbage-collected tables for remote values keyed by name or sha256(name).
	if getgc and bit32 then
		local hashed = sha256(name)
		local ok, gc = pcall(getgc, true)

		if ok and typeof(gc) == "table" then
			for _, value in next, gc do
				if typeof(value) ~= "table" then
					continue
				end

				if getrawmetatable and getrawmetatable(value) then
					continue
				end

				for key, item in next, value do
					if (key == name or key == hashed) and isRemote(item) then
						RemoteResolver.cache[pathOrName] = item
						return item
					end

					if isRemote(item) and item.Name == name then
						RemoteResolver.cache[pathOrName] = item
						return item
					end
				end
			end
		end
	end

	return nil
end

---@param inst Instance
---@return Instance?
local function resolveInstancePath(path)
	return walkPath(path)
end

---Substitute special markers in user-typed template args.
---@param args table
---@return table
function RemoteResolver.substituteArgs(args)
	local out = {}
	local character = localPlayer and localPlayer.Character
	local root = character and character:FindFirstChild("HumanoidRootPart")
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")
	local mouse = localPlayer and localPlayer:GetMouse()
	local camera = workspace and workspace.CurrentCamera

	for idx, value in next, args do
		local resolved = value

		if typeof(value) == "string" then
			if value == "$LOCALPLAYER" then
				resolved = localPlayer
			elseif value == "$CHARACTER" then
				resolved = character
			elseif value == "$ROOT" then
				resolved = root
			elseif value == "$HUMANOID" then
				resolved = humanoid
			elseif value == "$TICK" then
				resolved = os.clock()
			elseif value == "$MOUSEHIT" then
				resolved = mouse and mouse.Hit or CFrame.new()
			elseif value == "$CAMERA_CF" then
				resolved = camera and camera.CFrame or CFrame.new()
			elseif value == "$AIM_POS" then
				resolved = Vector3.zero
				pcall(function()
					if not camera then
						return
					end

					local origin = camera.CFrame.Position
					local direction = camera.CFrame.LookVector * 1000
					local params = RaycastParams.new()
					params.FilterType = Enum.RaycastFilterType.Exclude
					params.FilterDescendantsInstances = character and { character } or {}

					local hit = workspace:Raycast(origin, direction, params)

					resolved = (hit and hit.Position) or (origin + direction)
				end)
			elseif value:sub(1, 6) == "$ENUM:" then
				resolved = nil

				local enumText = value:sub(7)
				local familyName, itemName = enumText:match("^([^%.]+)%.(.+)$")

				if familyName and itemName then
					local ok, enumValue = pcall(function()
						return Enum[familyName][itemName]
					end)

					if ok and enumValue ~= nil then
						resolved = enumValue
					else
						Logger.warn("Could not resolve enum marker '%s'.", value)
					end
				else
					Logger.warn("Malformed enum marker '%s' (expected $ENUM:Family.Item).", value)
				end
			elseif value:sub(1, 10) == "$INSTANCE:" then
				resolved = resolveInstancePath(value:sub(11))
			end
		elseif typeof(value) == "table" then
			if value.__type == "CFrame" and value.components then
				resolved = CFrame.new(unpackFn(value.components))
			elseif value.__type == "Vector3" and value.components then
				resolved = Vector3.new(unpackFn(value.components))
			elseif value.__type == "Vector2" and value.components then
				resolved = Vector2.new(unpackFn(value.components))
			else
				resolved = RemoteResolver.substituteArgs(value)
			end
		end

		out[idx] = resolved
	end

	return out
end

---Fire a remote template.
---@param template RemoteTemplate
---@return boolean, any
function RemoteResolver.fire(template)
	if not template then
		return false, "No remote template."
	end

	local remote = RemoteResolver.resolve(template.path or template.name)

	if not remote then
		Logger.warn("Could not resolve remote '%s'.", template.path or template.name)
		return false, "Unresolved remote."
	end

	local method = template.method or "FireServer"

	if method ~= "FireServer" and method ~= "InvokeServer" then
		method = "FireServer"
	end

	local args = RemoteResolver.substituteArgs(template.args or {})

	if method == "InvokeServer" then
		-- InvokeServer yields for a response; spawn it so the defense thread isn't blocked.
		task.spawn(function()
			local ok, err = pcall(remote[method], remote, unpackFn(args))

			if not ok then
				RemoteResolver.cache[template.path or template.name] = nil
				Logger.warn("Remote '%s' failed: %s", template.path or template.name, err)
			end
		end)

		return true
	end

	local ok, err = pcall(remote[method], remote, unpackFn(args))

	if not ok then
		RemoteResolver.cache[template.path or template.name] = nil
		Logger.warn("Remote '%s' failed: %s", template.path or template.name, err)
	end

	return ok, err
end

---Built-in remote templates for known games.
local RemotePresets = {
	ABS = {
		Parry = {
			path = 'game:GetService("Players").LocalPlayer.Remotes.RequestAction',
			method = "InvokeServer",
			args = {
				"Parry",
				"$ENUM:UserInputState.End",
				{ MouseLock = false, MousePosition = "$AIM_POS" },
			},
		},
		Dodge = {
			path = 'game:GetService("Players").LocalPlayer.Remotes.RequestAction',
			method = "InvokeServer",
			args = {
				"Roll",
				"$ENUM:UserInputState.Begin",
				{ MouseLock = false, MousePosition = "$AIM_POS" },
			},
		},
	},
}

---Persist a remote template into per-game data.
---@param name string
---@param template RemoteTemplate
local function saveRemoteTemplate(name, template)
	GameDataRemotes()[name] = {
		path = template.path,
		method = template.method,
		args = template.args,
		name = name,
	}

	-- Saving a template re-enables that kind.
	GameDataRemotesDisabled()[name] = nil

	GameData.save()
end

---@return table
function GameDataRemotes()
	GameData.data.remotes = GameData.data.remotes or {}
	return GameData.data.remotes
end

---Per-game map of remote kinds the user disabled without deleting.
---@return table
function GameDataRemotesDisabled()
	GameData.data.remotesDisabled = GameData.data.remotesDisabled or {}
	return GameData.data.remotesDisabled
end

--------------------------------------------------------------------------------
-- Input
--------------------------------------------------------------------------------

local Latency = {}

---Get round-trip time in seconds.
---@return number
function Latency.rtt()
	local ok, value = pcall(function()
		return stats.Network.ServerStatsItem["Data Ping"]:GetValue() / 1000
	end)

	if ok and type(value) == "number" then
		return value
	end

	return 0
end

---@class Input
local Input = {
	lastParryAt = 0,
	lastNoTemplateWarn = 0,
	blockHeld = false,
}

---Press a key (or mouse button) via VirtualInputManager.
---@param keyName string
---@param holdSeconds number?
function Input.pressKey(keyName, holdSeconds)
	if not keyName or #keyName == 0 then
		return
	end

	holdSeconds = holdSeconds or ((Options and Options.KeyHoldTime and Options.KeyHoldTime.Value) or 50) / 1000

	if keyName == "MB1" or keyName == "MB2" then
		local button = keyName == "MB1" and 0 or 1
		local position = userInputService:GetMouseLocation()

		pcall(function()
			virtualInputManager:SendMouseButtonEvent(position.X, position.Y, button, true, game, 1)
		end)

		task.wait(holdSeconds)

		pcall(function()
			virtualInputManager:SendMouseButtonEvent(position.X, position.Y, button, false, game, 1)
		end)

		return
	end

	local ok, keyCode = pcall(function()
		return Enum.KeyCode[keyName]
	end)

	if not ok or not keyCode then
		Logger.warn("Unknown key '%s'.", keyName)
		return
	end

	pcall(function()
		virtualInputManager:SendKeyEvent(true, keyCode, false, game)
	end)

	task.wait(holdSeconds)

	pcall(function()
		virtualInputManager:SendKeyEvent(false, keyCode, false, game)
	end)
end

---Fire the remote template for a defense kind, if remote mode is active.
---@param kind string
---@return boolean
local function fireDefenseRemote(kind)
	if not Options or not Options.DefenseMode or Options.DefenseMode.Value ~= "Remote" then
		return false
	end

	local template = GameDataRemotes()[kind]

	if GameDataRemotesDisabled()[kind] then
		template = nil
	end

	if template then
		RemoteResolver.fire(template)
		return true
	end

	if os.clock() - Input.lastNoTemplateWarn > 5 then
		Input.lastNoTemplateWarn = os.clock()
		Logger.warn("Remote mode is on but no '%s' template is set; falling back to key emulation.", kind)
	end

	return false
end

---Perform a parry.
function Input.parry()
	if fireDefenseRemote("Parry") then
		Input.lastParryAt = os.clock()
		return
	end

	local key = (Options and Options.ParryKey and Options.ParryKey.Value) or "F"
	Input.lastParryAt = os.clock()
	task.spawn(Input.pressKey, key)
end

---Perform a dodge.
function Input.dodge()
	if fireDefenseRemote("Dodge") then
		return
	end

	local key = (Options and Options.DodgeKey and Options.DodgeKey.Value) or "Q"
	task.spawn(Input.pressKey, key)
end

---Hold or release block.
---@param start boolean
function Input.block(start)
	local remoteKind = start and "Start Block" or "End Block"

	if fireDefenseRemote(remoteKind) then
		Input.blockHeld = start
		return
	end

	local key = (Options and Options.ParryKey and Options.ParryKey.Value) or "F"

	if key == "MB1" or key == "MB2" then
		local button = key == "MB1" and 0 or 1
		local position = userInputService:GetMouseLocation()

		pcall(function()
			virtualInputManager:SendMouseButtonEvent(position.X, position.Y, button, start, game, 1)
		end)
	else
		local ok, keyCode = pcall(function()
			return Enum.KeyCode[key]
		end)

		if ok and keyCode then
			pcall(function()
				virtualInputManager:SendKeyEvent(start, keyCode, false, game)
			end)
		end
	end

	Input.blockHeld = start
end

---Jump.
function Input.jump()
	local character = localPlayer and localPlayer.Character
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")

	local ok = pcall(function()
		if humanoid then
			humanoid.Jump = true
		end
	end)

	if not ok or not humanoid then
		task.spawn(Input.pressKey, "Space")
	end
end

---Get the local player's HumanoidRootPart.
---@return BasePart?
function Input.localRoot()
	local character = localPlayer and localPlayer.Character

	return character and character:FindFirstChild("HumanoidRootPart")
end

--------------------------------------------------------------------------------
-- Hitbox
--------------------------------------------------------------------------------

---@class Hitbox
local Hitbox = {
	visualizeParts = {},
}

---Check whether the local root is inside the entity's hitbox.
---@param entityRoot BasePart
---@param localRoot BasePart
---@param size Vector3
---@param facingOffset boolean
---@param shiftOffset number
---@param visualize boolean
---@return boolean
function Hitbox.check(entityRoot, localRoot, size, facingOffset, shiftOffset, visualize)
	if not entityRoot or not localRoot or not size then
		return true
	end

	if size.Magnitude == 0 then
		return true
	end

	local cframe = entityRoot.CFrame

	if facingOffset then
		cframe = cframe * CFrame.new(0, 0, -size.Z / 2)
	end

	if shiftOffset and shiftOffset ~= 0 then
		cframe = cframe * CFrame.new(0, 0, shiftOffset)
	end

	local relative = cframe:PointToObjectSpace(localRoot.Position)
	local inside = math.abs(relative.X) <= size.X / 2
		and math.abs(relative.Y) <= size.Y / 2
		and math.abs(relative.Z) <= size.Z / 2

	if visualize then
		Hitbox.visualize(cframe, size, inside)
	end

	return inside
end

---Spawn a transient hitbox visualization part.
---@param cframe CFrame
---@param size Vector3
---@param inside boolean
function Hitbox.visualize(cframe, size, inside)
	local lifetime = (Options and Options.VisualizeLifetime and Options.VisualizeLifetime.Value) or 0.5

	pcall(function()
		local part = Instance.new("Part")
		part.Anchored = true
		part.CanCollide = false
		part.CanQuery = false
		part.CanTouch = false
		part.CastShadow = false
		part.Material = Enum.Material.ForceField
		part.Transparency = 0.5
		part.Size = size
		part.CFrame = cframe
		part.Color = inside and Color3.fromRGB(0, 255, 0) or Color3.fromRGB(255, 0, 0)
		part.Parent = workspace

		table.insert(Hitbox.visualizeParts, part)
		debris:AddItem(part, lifetime)
	end)
end

---Remove all visualization parts.
function Hitbox.clean()
	for _, part in next, Hitbox.visualizeParts do
		pcall(function()
			part:Destroy()
		end)
	end

	table.clear(Hitbox.visualizeParts)
end

---Compute the effective hitbox size for an action on a timing.
---@param action Action
---@param timing Timing
---@return Vector3
function Hitbox.effectiveSize(action, timing)
	if timing.duih then
		return timing.hitbox
	end

	if action.hitbox and action.hitbox.Magnitude ~= 0 then
		return action.hitbox
	end

	return timing.hitbox
end

--------------------------------------------------------------------------------
-- PlaybackData
--------------------------------------------------------------------------------

---@class PlaybackData
---@field base number Timestamp of when the object was created.
---@field ash table<number, number> Animation speed history. The key is the timestamp delta and the value is the speed at that point.
---@field entity Model Entity to playback.
local PlaybackData = {}
PlaybackData.__index = PlaybackData

---Get last exceeded speed difference from a timestamp delta.
---@param from number
---@return number?, number?
function PlaybackData:last(from)
	local latestExceededSpeed = nil
	local latestExceededDelta = nil

	for delta, speed in next, self.ash do
		if from <= delta then
			continue
		end

		if latestExceededDelta and delta <= latestExceededDelta then
			continue
		end

		latestExceededSpeed = speed
		latestExceededDelta = delta
	end

	return latestExceededSpeed, latestExceededDelta
end

---Track animation speed.
---@param speed number
function PlaybackData:astrack(speed)
	local delta = os.clock() - self.base

	if self:last(delta) == speed then
		return
	end

	self.ash[delta] = speed
end

---Create new PlaybackData object.
---@param entity Model
---@return PlaybackData
function PlaybackData.new(entity)
	local self = setmetatable({}, PlaybackData)
	self.base = os.clock()
	self.entity = entity

	---@note: Timestamp delta is how many seconds need to pass before being able to reach this speed.
	self.ash = {}

	return self
end

--------------------------------------------------------------------------------
-- Forward declarations
--------------------------------------------------------------------------------

local Defense
local InfoLogger
local DifferenceCalculator
local Entities
local AnimationVisualizer
local AutoLearn
local refreshAllSections

--------------------------------------------------------------------------------
-- Entities (universal entity discovery)
--------------------------------------------------------------------------------

---@class Entities
Entities = {
	tracked = {}, -- model -> state { maid, humanoid, lastTrack, lastAt, pbdata, rpbdata }
	deletedPlaybackData = {}, -- entity name -> rpbdata for removed entities
	maid = Maid.new(),
}

local DELETED_PLAYBACK_MAX = 50

---Resolve an entity's root part. Works for NPCs without a HumanoidRootPart.
---@param model any
---@return BasePart?
local function entityRoot(model)
	if typeof(model) ~= "Instance" then
		return nil
	end

	local humanoid = model:FindFirstChildOfClass("Humanoid")

	if humanoid and humanoid.RootPart then
		return humanoid.RootPart
	end

	local root = model:FindFirstChild("HumanoidRootPart")

	if root then
		return root
	end

	return model.PrimaryPart
end

---Is a model a valid entity? Requires a Humanoid, or an AnimationController with any root part.
---@param model any
---@return boolean
local function isEntity(model)
	if typeof(model) ~= "Instance" or not model:IsA("Model") then
		return false
	end

	if model:FindFirstChildOfClass("Humanoid") then
		return true
	end

	-- AnimationController-driven NPCs still need a root part to validate distance.
	if
		model:FindFirstChildOfClass("AnimationController")
		and (model:FindFirstChild("HumanoidRootPart") or model.PrimaryPart)
	then
		return true
	end

	return false
end

---Distance between the local root and an entity.
---@param entity Model
---@return number?
local function entityDistance(entity)
	local localRoot = Input.localRoot()
	local root = entity and entityRoot(entity)

	if not localRoot or not root then
		return nil
	end

	return (localRoot.Position - root.Position).Magnitude
end

---Is an entity owned by a player?
---@param entity Model
---@return boolean
local function isPlayerEntity(entity)
	return players:GetPlayerFromCharacter(entity) ~= nil
end

---@param entity Model
---@param track AnimationTrack
local function handleAnimationPlayed(entity, track)
	if UNLOADED then
		return
	end

	local state = Entities.tracked[entity]

	if not state then
		return
	end

	local now = os.clock()

	-- Dedupe the same track firing from both Humanoid and Animator signals.
	if state.lastTrack == track and now - state.lastAt < 0.05 then
		return
	end

	state.lastTrack = track
	state.lastAt = now

	-- Record playback data for the animation visualizer (all animations, timing or not).
	if Toggles and Toggles.ShowAnimationVisualizer and Toggles.ShowAnimationVisualizer.Value then
		state.pbdata[track] = PlaybackData.new(entity)
	end

	local maxDistance = (Options and Options.MaxDetectionDistance and Options.MaxDetectionDistance.Value) or 300
	local distance = entityDistance(entity)

	if distance and distance > maxDistance then
		return
	end

	if DifferenceCalculator then
		DifferenceCalculator.onAnimation(entity, track)
	end

	if AutoLearn then
		AutoLearn.onAnimation(entity, track)
	end

	if Defense then
		Defense.onAnimation(entity, track)
	end
end

---Hook an entity model's humanoid, animator, sounds and added descendants.
---@param entity Model
local function hookEntity(entity)
	if Entities.tracked[entity] then
		return
	end

	local maid = Maid.new()
	local humanoid = entity:FindFirstChildOfClass("Humanoid")
	local controller = entity:FindFirstChildOfClass("AnimationController")

	local state = {
		maid = maid,
		humanoid = humanoid,
		lastTrack = nil,
		lastAt = 0,
		pbdata = {},
		rpbdata = {},
	}

	Entities.tracked[entity] = state

	-- Animation signals (Humanoid or AnimationController as host).
	local host = humanoid or controller

	if host then
		maid:mark(host.AnimationPlayed:Connect(function(track)
			handleAnimationPlayed(entity, track)
		end))
	end

	local function hookAnimator(animator)
		if not animator then
			return
		end

		maid:mark(animator.AnimationPlayed:Connect(function(track)
			handleAnimationPlayed(entity, track)
		end))
	end

	local animator = entity:FindFirstChildWhichIsA("Animator", true)

	if animator then
		hookAnimator(animator)
	elseif host then
		maid:mark(host.ChildAdded:Connect(function(child)
			if child:IsA("Animator") then
				hookAnimator(child)
			end
		end))

		maid:mark(entity.DescendantAdded:Connect(function(child)
			if child:IsA("Animator") then
				hookAnimator(child)
			end
		end))
	end

	-- Effect / sound descendant detection.
	maid:mark(entity.DescendantAdded:Connect(function(inst)
		if UNLOADED then
			return
		end

		if inst:IsA("Sound") then
			if Defense then
				Defense.onSound(entity, inst)
			end

			maid:mark(inst.Played:Connect(function()
				if Defense then
					Defense.onSound(entity, inst)
				end
			end))

			maid:mark(inst:GetPropertyChangedSignal("IsPlaying"):Connect(function()
				if inst.IsPlaying and Defense then
					Defense.onSound(entity, inst)
				end
			end))
		elseif Defense then
			Defense.onEffect(entity, inst)
		end
	end))

	-- Existing playing sounds.
	for _, inst in next, entity:GetDescendants() do
		if inst:IsA("Sound") and inst.IsPlaying and Defense then
			Defense.onSound(entity, inst)
		end
	end

	-- Cleanup when the entity is removed; keep its recorded playback data around.
	maid:mark(entity.AncestryChanged:Connect(function()
		if not entity:IsDescendantOf(workspace) then
			local tracked = Entities.tracked[entity]

			if tracked then
				if next(tracked.rpbdata) then
					Entities.deletedPlaybackData[entity.Name] = tracked.rpbdata

					local count = 0
					for _ in next, Entities.deletedPlaybackData do
						count = count + 1
					end

					if count > DELETED_PLAYBACK_MAX then
						local firstKey = next(Entities.deletedPlaybackData)
						Entities.deletedPlaybackData[firstKey] = nil
					end
				end

				tracked.maid:clean()
				Entities.tracked[entity] = nil
			end
		end
	end))
end

---Initial scan + watch for new entities.
function Entities.start()
	local localCharacter = localPlayer and localPlayer.Character

	for _, inst in next, workspace:GetDescendants() do
		if inst:IsA("Humanoid") then
			local model = inst.Parent

			if
				isEntity(model)
				and model ~= localCharacter
				and not Entities.tracked[model]
				and not (
					Toggles
					and Toggles.OnlyTargetPlayers
					and Toggles.OnlyTargetPlayers.Value
					and not isPlayerEntity(model)
				)
			then
				hookEntity(model)
			end
		end
	end

	Entities.maid:mark(workspace.DescendantAdded:Connect(function(inst)
		if UNLOADED or not inst:IsA("Humanoid") then
			return
		end

		task.defer(function()
			local model = inst.Parent

			if not isEntity(model) or model == (localPlayer and localPlayer.Character) then
				return
			end

			if
				Toggles
				and Toggles.OnlyTargetPlayers
				and Toggles.OnlyTargetPlayers.Value
				and not isPlayerEntity(model)
			then
				return
			end

			hookEntity(model)
		end)
	end))

	-- Part timings fire on any matching BasePart added anywhere.
	Entities.maid:mark(workspace.DescendantAdded:Connect(function(inst)
		if UNLOADED or not inst:IsA("BasePart") or not Defense then
			return
		end

		Defense.onPart(inst)
	end))

	-- Track the local character for respawns.
	Entities.maid:mark(localPlayer.CharacterAdded:Connect(function()
		Entities.rescan()
	end))
end

---Re-scan workspace for entities (e.g. after respawn).
function Entities.rescan()
	for model, state in next, Entities.tracked do
		if not model:IsDescendantOf(workspace) then
			state.maid:clean()
			Entities.tracked[model] = nil
		end
	end

	Entities.start()
end

---Find the nearest tracked entity to a position.
---@param position Vector3
---@return Model?
function Entities.nearest(position)
	local best, bestDistance = nil, math.huge

	for model in next, Entities.tracked do
		local root = entityRoot(model)

		if root then
			local distance = (root.Position - position).Magnitude

			if distance < bestDistance then
				best = model
				bestDistance = distance
			end
		end
	end

	return best
end

---Track animation speeds for the visualizer every Heartbeat.
function Entities.trackPlayback()
	local enabled = Toggles and Toggles.ShowAnimationVisualizer and Toggles.ShowAnimationVisualizer.Value

	for _, state in next, Entities.tracked do
		for track, data in next, state.pbdata do
			if not enabled then
				state.pbdata[track] = nil
				continue
			end

			if not track.IsPlaying then
				state.pbdata[track] = nil
				state.rpbdata[normalizeAssetId(track.Animation and track.Animation.AnimationId or "")] = data
				continue
			end

			data:astrack(track.Speed)
		end
	end
end

---Get recorded playback data for an animation id.
---@param aid string
---@return PlaybackData?
function Entities.agpd(aid)
	local normalized = normalizeAssetId(aid)

	-- Grab from 'rpbdata' — data there has been fully recorded.
	for _, state in next, Entities.tracked do
		local data = state.rpbdata[aid] or state.rpbdata[normalized]

		if data then
			return data
		end
	end

	-- Fallback to deleted playback data.
	for _, rpbdata in next, Entities.deletedPlaybackData do
		local data = rpbdata[aid] or rpbdata[normalized]

		if data then
			return data
		end
	end

	return nil
end

--------------------------------------------------------------------------------
-- ScreenGui helper
--------------------------------------------------------------------------------

---Create a ScreenGui parented to a hidden/core UI container.
---@param name string
---@return ScreenGui
local function createScreenGui(name)
	local gui = Instance.new("ScreenGui")
	gui.Name = name
	gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling

	local parented = false

	if gethui then
		parented = pcall(function()
			gui.Parent = gethui()
		end)
	end

	if not parented then
		parented = pcall(function()
			gui.Parent = game:GetService("CoreGui")
		end)
	end

	if not parented and localPlayer then
		pcall(function()
			gui.Parent = localPlayer:FindFirstChildOfClass("PlayerGui")
		end)
	end

	return gui
end

--------------------------------------------------------------------------------
-- InfoLogger
--------------------------------------------------------------------------------

---@class InfoLogger
InfoLogger = {
	Cycles = { "Animation", "Part", "Sound", "Effect" },
	Cycle = 1,
	Data = {
		MissingDataEntries = {},
		KeyBlacklistHistory = {},
		KeyBlacklistList = {},
	},
	queue = {},
	frame = nil,
	label = nil,
	container = nil,
	lastClickedKey = nil,
}

---Current key blacklist (persisted per game).
---@return table
local function blacklist()
	GameData.data.blacklist = GameData.data.blacklist or {}
	InfoLogger.Data.KeyBlacklistList = GameData.data.blacklist
	return InfoLogger.Data.KeyBlacklistList
end

---Persist the blacklist.
local function saveBlacklist()
	GameData.data.blacklist = InfoLogger.Data.KeyBlacklistList
	GameData.save()
end

---@return string[]
function InfoLogger.keyBlacklists()
	local tbl = {}

	for key, val in next, blacklist() do
		if not val then
			continue
		end

		tbl[#tbl + 1] = key
	end

	return tbl
end

---Refresh the info logger entries.
function InfoLogger.refresh()
	local currentType = InfoLogger.Cycles[InfoLogger.Cycle]
	local blacklistList = blacklist()

	for idx, entry in next, InfoLogger.Data.MissingDataEntries do
		if not blacklistList[entry.Key] then
			continue
		end

		table.remove(InfoLogger.Data.MissingDataEntries, idx)
		pcall(entry.Label.Destroy, entry.Label)
	end

	for idx, entry in next, InfoLogger.Data.MissingDataEntries do
		entry.Label.Parent = entry.Type == currentType and InfoLogger.container or nil
		entry.Label.LayoutOrder = idx
	end

	InfoLogger.label.Text = string.format("Info Logger (%s)", currentType)

	local ySize = 0
	local xSize = 0

	for _, entry in next, InfoLogger.Data.MissingDataEntries do
		if not entry.Label.Parent then
			continue
		end

		ySize = ySize + entry.Label.TextBounds.Y + 2

		if entry.Label.TextBounds.X <= xSize then
			continue
		end

		xSize = entry.Label.TextBounds.X
	end

	xSize = xSize + 20
	ySize = ySize + 22

	InfoLogger.frame.Size = UDim2.new(0, math.clamp(xSize, 210, 800), 0, math.clamp(ySize, 24, 180))
end

---Queue a miss entry. One queued entry is processed per RenderStepped; the queue is
---discarded while the logger is hidden.
---@param type string
---@param key string
---@param name string?
---@param distance number
---@param parent string?
function InfoLogger.addMissEntry(entryType, key, name, distance, parent)
	local ifd = InfoLogger.Data
	local mde = ifd.MissingDataEntries
	local bl = blacklist()

	if bl[key] then
		return
	end

	table.insert(InfoLogger.queue, 1, function()
		local function getEntriesForThisType()
			local entries = {}

			for idx, entry in next, mde do
				if entry.Type == entryType then
					table.insert(entries, { entry, idx })
				end
			end

			return entries
		end

		-- Pop the last element if we're over 30 entries for this type.
		local entries = getEntriesForThisType()
		local last = entries[#entries]

		if #entries > 30 and last then
			last[1].Label:Destroy()
			table.remove(mde, last[2])
		end

		local asset = nil

		if (entryType == "Animation" or entryType == "Sound") and typeof(key) == "string" then
			asset = tonumber(normalizeAssetId(key):match("%d+") or "")
		end

		-- Create a new label.
		local label = Library:CreateLabel({
			Text = name and string.format("(%.2fm away) Key '%s' from '%s' is missing.", distance, key, name)
				or string.format("(%.2fm away) Key '%s' is missing.", distance, key),
			TextXAlignment = Enum.TextXAlignment.Left,
			Size = UDim2.new(1, 0, 0, 14),
			LayoutOrder = 1,
			TextSize = 12,
			Visible = true,
			ZIndex = 306,
			Parent = nil,
		}, true)

		if parent then
			label.Text = string.format("(%s) %s", parent, label.Text)
		end

		Library:AddToRegistry(label, {
			TextColor3 = "FontColor",
		}, true)

		if asset then
			task.spawn(function()
				pcall(function()
					local info = game:GetService("MarketplaceService"):GetProductInfo(asset)

					if not info then
						return
					end

					label.Text = string.format("(%s) %s", info.Name, label.Text)
				end)
			end)
		end

		-- entry
		local entry = { Label = label, Key = key, Type = entryType }

		-- Copy & blacklist.
		label.InputBegan:Connect(function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				InfoLogger.lastClickedKey = key

				if setclipboard then
					setclipboard(key)
				end

				Library:Notify(string.format("Copied key '%s' to clipboard.", key))
			end

			if input.UserInputType == Enum.UserInputType.MouseButton2 then
				blacklist()[key] = true
				ifd.KeyBlacklistHistory[#ifd.KeyBlacklistHistory + 1] = key
				saveBlacklist()
				InfoLogger.refresh()

				if Options and Options.BlacklistedKeys then
					Options.BlacklistedKeys:SetValues(InfoLogger.keyBlacklists())
				end

				Library:Notify(string.format("Blacklisted key '%s' from list.", key))
			end
		end)

		-- Create a new entry for later destroying.
		table.insert(mde, 1, entry)

		-- Refresh.
		InfoLogger.refresh()
	end)
end

---Process one queued miss entry per RenderStepped; discard the queue while hidden.
function InfoLogger.renderStepped()
	if not InfoLogger.frame or not InfoLogger.frame.Visible then
		table.clear(InfoLogger.queue)
		return
	end

	local work = table.remove(InfoLogger.queue)

	if work then
		work()
	end
end

---Log a miss, gated by the window visibility and distance sliders.
---@param entryType string
---@param key string
---@param name string?
---@param distance number
---@param parent string?
---@return boolean
function InfoLogger.miss(entryType, key, name, distance, parent)
	if not (Toggles and Toggles.ShowLoggerWindow and Toggles.ShowLoggerWindow.Value) then
		return false
	end

	local minDistance = (Options and Options.MinimumLoggerDistance and Options.MinimumLoggerDistance.Value) or 0
	local maxDistance = (Options and Options.MaximumLoggerDistance and Options.MaximumLoggerDistance.Value) or 1000

	if distance and (distance < minDistance or distance > maxDistance) then
		return false
	end

	InfoLogger.addMissEntry(entryType, key, name, distance or 0, parent)
	return true
end

---Set the logger window visibility.
---@param state boolean
function InfoLogger.visible(state)
	if InfoLogger.frame then
		InfoLogger.frame.Visible = state
	end
end

---Build the Info Logger window (requires the Linoria library to be loaded).
function InfoLogger.init()
	local screenGui = createScreenGui("UAPB_InfoLogger")
	InfoLogger.screenGui = screenGui

	blacklist()

	local outer = Library:Create("Frame", {
		BorderColor3 = Color3.new(0, 0, 0),
		Position = UDim2.new(0, 15, 0.5, 0),
		Size = UDim2.new(0, 210, 0, 20),
		Visible = false,
		ZIndex = 287,
		Parent = screenGui,
	})

	local inner = Library:Create("Frame", {
		BackgroundColor3 = Library.MainColor,
		BorderColor3 = Library.OutlineColor,
		BorderMode = Enum.BorderMode.Inset,
		Size = UDim2.new(1, 0, 1, 0),
		ZIndex = 288,
		Parent = outer,
	})

	Library:AddToRegistry(inner, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "OutlineColor",
	}, true)

	local colorFrame = Library:Create("Frame", {
		BackgroundColor3 = Library.AccentColor,
		BorderSizePixel = 0,
		Size = UDim2.new(1, 0, 0, 2),
		ZIndex = 299,
		Parent = inner,
	})

	Library:AddToRegistry(colorFrame, {
		BackgroundColor3 = "AccentColor",
	}, true)

	local loggerLabel = Library:CreateLabel({
		Size = UDim2.new(1, 0, 0, 20),
		Position = UDim2.fromOffset(5, 2),
		TextXAlignment = Enum.TextXAlignment.Left,
		TextColor3 = Library.AccentColor,
		Text = "Info Logger",
		TextSize = 14,
		ZIndex = 300,
		Parent = inner,
	})

	Library:AddToRegistry(loggerLabel, {
		TextColor3 = "AccentColor",
	}, true)

	local container = Library:Create("ScrollingFrame", {
		BackgroundTransparency = 1,
		Size = UDim2.new(1, 0, 1, -20),
		Position = UDim2.new(0, 0, 0, 20),
		ZIndex = 1,
		ScrollBarThickness = 0,
		Parent = inner,
	})

	local listLayout = Library:Create("UIListLayout", {
		FillDirection = Enum.FillDirection.Vertical,
		SortOrder = Enum.SortOrder.LayoutOrder,
		Parent = container,
	})

	listLayout:GetPropertyChangedSignal("AbsoluteContentSize"):Connect(function()
		container.CanvasSize = UDim2.fromOffset(0, listLayout.AbsoluteContentSize.Y)
	end)

	Library:Create("UIPadding", {
		PaddingLeft = UDim.new(0, 5),
		Parent = container,
	})

	rootMaid:mark(outer.InputBegan:Connect(function(inputObject)
		if inputObject.UserInputType ~= Enum.UserInputType.Keyboard then
			return
		end

		if inputObject.KeyCode == Enum.KeyCode.Z and userInputService:IsKeyDown(Enum.KeyCode.LeftControl) then
			local history = InfoLogger.Data.KeyBlacklistHistory
			local front = history[1]

			if not front then
				return
			end

			blacklist()[front] = nil
			table.remove(history, 1)
			saveBlacklist()
			InfoLogger.refresh()

			if Options and Options.BlacklistedKeys then
				Options.BlacklistedKeys:SetValues(InfoLogger.keyBlacklists())
			end

			Library:Notify(string.format("Re-whitelisted key '%s' into list.", front))
		end

		if inputObject.KeyCode == Enum.KeyCode.Q then
			InfoLogger.Cycle = math.max(InfoLogger.Cycle - 1, 1)
			InfoLogger.refresh()
		end

		if inputObject.KeyCode == Enum.KeyCode.E then
			InfoLogger.Cycle = math.min(InfoLogger.Cycle + 1, #InfoLogger.Cycles)
			InfoLogger.refresh()
		end
	end))

	InfoLogger.label = loggerLabel
	InfoLogger.frame = outer
	InfoLogger.container = container
	InfoLogger.Cycle = 1

	Library:MakeDraggable(outer)
	InfoLogger.refresh()
end

---Destroy the Info Logger window.
function InfoLogger.detach()
	if InfoLogger.screenGui then
		pcall(function()
			InfoLogger.screenGui:Destroy()
		end)

		InfoLogger.screenGui = nil
	end
end

--------------------------------------------------------------------------------
-- AnimationVisualizer
--------------------------------------------------------------------------------

---@note: This code is UI code. It is ugly on purpose and lazily made.
---@class AnimationVisualizer
AnimationVisualizer = {}

local visualizerMaid = Maid.new()

local visualizerScreenGui = nil
local outer = nil
local inner = nil
local animationVisualizerLabel = nil
local sliderOuter = nil
local sliderText = nil
local sliderFill = nil
local hideBorderRight = nil
local frameBackwards = nil
local icon = nil
local playStop = nil
local iconTwo = nil
local viewportFrame = nil
local worldModel = nil
local camera = nil
local speedText = nil
local noViewportFrame = nil
local textLabel = nil
local colorFrame = nil
local frameForwards = nil
local iconThree = nil
local animationTextbox = nil

-- Current data for playback loop.
local currentPlaybackData = nil
local currentTrack = nil
local isPaused = false
local timeElapsed = 0.0

---Map slider value.
---@param value number
---@param min number
---@param max number
---@param minSize number
---@param maxSize number
local function mapSliderValue(value, min, max, minSize, maxSize)
	return (1 - ((value - min) / (max - min))) * minSize + ((value - min) / (max - min)) * maxSize
end

---On Animation ID focus lost.
---@param enter boolean
local function onIdFocusLost(enter)
	if not enter then
		return
	end

	-- Empty out previous data.
	currentTrack = nil
	currentPlaybackData = nil

	---@type PlaybackData
	local playbackData = Entities.agpd(animationTextbox.Text)

	if not playbackData then
		return AnimationVisualizer.message("No Playback Data Found")
	end

	-- Remove all previously loaded models.
	for _, descendant in next, viewportFrame:GetDescendants() do
		if descendant.ClassName ~= "Model" then
			continue
		end

		descendant:Destroy()
	end

	-- Load the model & center it.
	local entity = playbackData.entity:Clone()
	entity.Parent = worldModel
	entity:PivotTo(CFrame.new(0, 0, 0))

	-- Fetch the primary part. If it does not exist, then the entity has been unloaded.
	if not entity.PrimaryPart then
		return AnimationVisualizer.message("No Primary Part Found")
	end

	-- Setup camera.
	local _, bbs = entity:GetBoundingBox()
	camera.CFrame =
		CFrame.lookAt(entity.PrimaryPart.Position - Vector3.new(0, 0, bbs.Magnitude), entity.PrimaryPart.Position)

	-- Fetch animator.
	local animator = entity:FindFirstChildWhichIsA("Animator", true)

	if not animator then
		return AnimationVisualizer.message("No Animator Found")
	end

	-- Stop previous animations.
	for _, track in next, animator:GetPlayingAnimationTracks() do
		track:Stop()
	end

	-- Create animation.
	local animation = Instance.new("Animation")
	animation.AnimationId = animationTextbox.Text

	-- Store current data for playback.
	currentPlaybackData = playbackData
	currentTrack = animator:LoadAnimation(animation)

	-- Play animation and keep it at zero speed.
	currentTrack:Play(0.0, 100, 0.0)
	currentTrack.Priority = Enum.AnimationPriority.Action
	currentTrack.Looped = true
	visualizerMaid:mark(currentTrack.DidLoop:Connect(function()
		timeElapsed = 0.0
	end))

	-- Reset time elapsed.
	timeElapsed = 0.0

	-- Show frames.
	viewportFrame.Visible = true
	noViewportFrame.Visible = false
end

---Get time elapsed from time position.
---@param timePosition number
---@param animationLength number
---@return number?
local function getTimeElapsedFromTp(timePosition, animationLength)
	if not currentPlaybackData then
		return nil
	end

	if timePosition <= 0 then
		return 0.0
	end

	-- Numerical integration to find elapsed time.
	local currentPos = 0
	local elapsed = 0
	local dt = 0.01
	local iterations = 0

	while currentPos < timePosition do
		local speed = currentPlaybackData:last(elapsed) or 1
		local stepSize = speed * dt

		iterations = iterations + 1

		---@note: The iteration budget is the animation length at dt=0.01s times a 10x buffer; minimum 1000.
		if iterations >= math.max(animationLength * 100 * 10, 1000) then
			break
		end

		-- If adding the full step would exceed the target position, calculate partial step and break.
		if currentPos + stepSize > timePosition then
			local remainingTime = (timePosition - currentPos) / speed
			elapsed = elapsed + remainingTime
			break
		end

		currentPos = currentPos + stepSize
		elapsed = elapsed + dt
	end

	-- Return the elapsed time.
	return elapsed
end

---On playback loop.
---@param delta number
local function onPlaybackLoop(delta)
	if not visualizerScreenGui or not visualizerScreenGui.Enabled then
		return
	end

	iconTwo.Image = isPaused and "rbxassetid://10734923549" or "rbxassetid://10734919336"

	-- Run slider calculations.
	local mhs = sliderOuter.AbsoluteSize.X
	local hs = currentTrack and mapSliderValue(currentTrack.TimePosition, 0.0, currentTrack.Length, 0, mhs) or 0.0

	-- Update slider text.
	sliderText.Text = (currentTrack and currentPlaybackData)
			and string.format(
				"%.3f/%.3f (%ims)",
				currentTrack.TimePosition,
				currentTrack.Length,
				math.round((getTimeElapsedFromTp(currentTrack.TimePosition, currentTrack.Length) or 0.0) * 1000)
			)
		or "0.000 / ??? (???ms)"

	-- Update size.
	sliderFill.Visible = not (hs == 0)
	sliderFill.Size = UDim2.new(0, math.max(math.ceil(hs), 1), 1, 0)
	hideBorderRight.Visible = not (hs == mhs or hs == 0)

	-- Update speed amount.
	speedText.Text = currentTrack and string.format("Speed (%.2f)", currentTrack.Speed) or "Speed (???)"

	if currentTrack and isPaused then
		speedText.Text = string.format(
			"Speed (%.2f)",
			currentPlaybackData:last(getTimeElapsedFromTp(currentTrack.TimePosition, currentTrack.Length) or 0.0) or 0.0
		)
	end

	if not currentTrack or not currentPlaybackData then
		return
	end

	if isPaused then
		return currentTrack:AdjustSpeed(0.0)
	end

	timeElapsed = timeElapsed + delta

	currentTrack:AdjustSpeed(currentPlaybackData:last(timeElapsed) or 0.0)
end

---Toggle play stop function.
local function togglePlayStop()
	if not currentTrack then
		return
	end

	if not currentTrack.IsPlaying then
		return
	end

	isPaused = not isPaused
end

---Go backwards one frame.
local function onFrameBackwards()
	if not currentTrack then
		return
	end

	currentTrack.TimePosition = math.max(currentTrack.TimePosition - 0.01, 0)
end

---Go forwards one frame.
local function onFrameForwards()
	if not currentTrack then
		return
	end

	currentTrack.TimePosition = math.min(currentTrack.TimePosition + 0.01, currentTrack.Length)
end

---On slider input began.
---@param input InputObject
---@param gameProcessed boolean
local function onSliderInputBegan(input, gameProcessed)
	if gameProcessed then
		return
	end

	if input.UserInputType ~= Enum.UserInputType.MouseButton1 then
		return
	end

	while visualizerScreenGui.Enabled and userInputService:IsMouseButtonPressed(Enum.UserInputType.MouseButton1) do
		if not currentTrack then
			return
		end

		-- Pause track.
		isPaused = true

		-- Calculate new time position.
		local mouse = localPlayer:GetMouse()
		local sliderOuterSize = sliderOuter.AbsoluteSize.X
		local mouseX = math.clamp(mouse.X - sliderOuter.AbsolutePosition.X, 0, sliderOuterSize)
		local newTimePosition = mapSliderValue(mouseX, 0, sliderOuterSize, 0, currentTrack.Length)

		-- Update time position.
		currentTrack.TimePosition = newTimePosition

		-- Wait.
		runService.PreRender:Wait()
	end

	timeElapsed = getTimeElapsedFromTp(currentTrack.TimePosition, currentTrack.Length) or 0.0
end

---Outer input began.
---@param input InputObject
---@param gameProcessed boolean
local function outerFrameInputBegan(input, gameProcessed)
	if gameProcessed then
		return
	end

	if input.KeyCode == Enum.KeyCode.Space then
		return togglePlayStop()
	end

	if input.KeyCode == Enum.KeyCode.Right then
		return onFrameForwards()
	end

	if input.KeyCode == Enum.KeyCode.Left then
		return onFrameBackwards()
	end
end

---Set the visibility of the AnimationVisualizer.
---@param state boolean
function AnimationVisualizer.visible(state)
	if visualizerScreenGui then
		visualizerScreenGui.Enabled = state
	end
end

---Show a message.
---@param message string
function AnimationVisualizer.message(message)
	viewportFrame.Visible = false
	noViewportFrame.Visible = true
	textLabel.Text = message
end

---Initialize AnimationVisualizer module (requires the Linoria library).
function AnimationVisualizer.init()
	visualizerScreenGui = createScreenGui("AnimationVisualizer")
	visualizerScreenGui.Enabled = false
	visualizerScreenGui.DisplayOrder = 1

	outer = Instance.new("Frame")
	outer.Name = "Outer"
	outer.BackgroundColor3 = Color3.new(1, 1, 1)
	outer.Position = UDim2.new(0.27, 0, 0.216, 0)
	outer.BorderColor3 = Color3.new()
	outer.Size = UDim2.new(0, 260, 0, 301.75)
	outer.ZIndex = 100
	outer.Parent = visualizerScreenGui

	inner = Instance.new("Frame")
	inner.Name = "Inner"
	inner.BackgroundColor3 = Library.MainColor
	inner.BorderMode = Enum.BorderMode.Inset
	inner.BorderColor3 = Library.OutlineColor
	inner.Size = UDim2.new(1, 0, 1, 0)
	inner.Parent = outer

	animationVisualizerLabel = Instance.new("TextLabel")
	animationVisualizerLabel.Name = "AnimationVisualizer"
	animationVisualizerLabel.FontFace = Font.new("rbxasset://fonts/families/RobotoMono.json")
	animationVisualizerLabel.TextColor3 = Library.AccentColor
	animationVisualizerLabel.Text = "Animation Visualizer"
	animationVisualizerLabel.BackgroundColor3 = Color3.new()
	animationVisualizerLabel.BorderSizePixel = 0
	animationVisualizerLabel.BackgroundTransparency = 1
	animationVisualizerLabel.Position = UDim2.new(0, 5, 0, 5)
	animationVisualizerLabel.TextXAlignment = Enum.TextXAlignment.Left
	animationVisualizerLabel.BorderColor3 = Color3.new()
	animationVisualizerLabel.TextSize = 17
	animationVisualizerLabel.Size = UDim2.new(1, 0, 0, 20)
	animationVisualizerLabel.Parent = inner

	sliderOuter = Instance.new("Frame")
	sliderOuter.Name = "SliderOuter"
	sliderOuter.BackgroundColor3 = Color3.new(1, 1, 1)
	sliderOuter.Position = UDim2.new(0.323, -78, 0.835, 24)
	sliderOuter.BorderColor3 = Color3.new()
	sliderOuter.BorderSizePixel = 0
	sliderOuter.Size = UDim2.new(0, 247, 0, 15)
	sliderOuter.Parent = inner

	sliderText = Instance.new("TextLabel")
	sliderText.Name = "SliderText"
	sliderText.FontFace = Font.new("rbxasset://fonts/families/RobotoMono.json")
	sliderText.TextColor3 = Library.FontColor
	sliderText.Text = "0.000 / ? (?ms)"
	sliderText.BackgroundTransparency = 1
	sliderText.BackgroundColor3 = Color3.new(1, 1, 1)
	sliderText.BorderSizePixel = 0
	sliderText.BorderColor3 = Color3.new()
	sliderText.TextSize = 12
	sliderText.ZIndex = 12
	sliderText.Size = UDim2.new(1, 0, 1, 0)
	sliderText.Parent = sliderOuter

	sliderFill = Instance.new("Frame")
	sliderFill.Name = "SliderFill"
	sliderFill.BorderMode = Enum.BorderMode.Inset
	sliderFill.BorderColor3 = Library.AccentColorDark
	sliderFill.BackgroundColor3 = Library.AccentColor
	sliderFill.Size = UDim2.new(0, 1, 1, 0)
	sliderFill.ZIndex = 10
	sliderFill.Parent = sliderOuter

	hideBorderRight = Instance.new("Frame")
	hideBorderRight.Name = "HideBorderRight"
	hideBorderRight.BackgroundColor3 = Library.AccentColor
	hideBorderRight.Position = UDim2.new(1, 0, 0, 0)
	hideBorderRight.BorderColor3 = Color3.new()
	hideBorderRight.BorderSizePixel = 0
	hideBorderRight.Size = UDim2.new(0, 1, 1, 0)
	hideBorderRight.Parent = sliderFill
	hideBorderRight.Visible = false

	local sliderInner = Instance.new("Frame")
	sliderInner.Name = "SliderInner"
	sliderInner.BorderColor3 = Color3.new()
	sliderInner.BackgroundColor3 = Library.MainColor
	sliderInner.Size = UDim2.new(1, 0, 1, 0)
	sliderInner.Parent = sliderOuter

	frameBackwards = Instance.new("TextButton")
	frameBackwards.Name = "FrameBackwards"
	frameBackwards.FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json")
	frameBackwards.TextColor3 = Color3.new()
	frameBackwards.Text = ""
	frameBackwards.Position = UDim2.new(0.323, -78, 0.835, -2)
	frameBackwards.BackgroundColor3 = Library.MainColor
	frameBackwards.BorderColor3 = Color3.new()
	frameBackwards.TextSize = 14
	frameBackwards.Size = UDim2.new(0, 70, 0, 20)
	frameBackwards.Parent = inner

	icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.ScaleType = Enum.ScaleType.Crop
	icon.BorderColor3 = Color3.new()
	icon.BackgroundColor3 = Library.FontColor
	icon.Image = "rbxassetid://10734961526"
	icon.BackgroundTransparency = 1
	icon.Position = UDim2.new(0.5, -8, 0.5, -8)
	icon.SizeConstraint = Enum.SizeConstraint.RelativeXX
	icon.BorderSizePixel = 0
	icon.Size = UDim2.new(0, 16, 0, 16)
	icon.Parent = frameBackwards

	playStop = Instance.new("TextButton")
	playStop.Name = "PlayStop"
	playStop.FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json")
	playStop.TextColor3 = Color3.new()
	playStop.BorderColor3 = Color3.new()
	playStop.Text = ""
	playStop.Position = UDim2.new(0.323, 0, 0.835, -2)
	playStop.BackgroundColor3 = Library.MainColor
	playStop.TextSize = 14
	playStop.Size = UDim2.new(0, 91, 0, 20)
	playStop.Parent = inner

	iconTwo = Instance.new("ImageLabel")
	iconTwo.Name = "Icon"
	iconTwo.BorderColor3 = Color3.new()
	iconTwo.BackgroundColor3 = Library.FontColor
	iconTwo.Image = "rbxassetid://10734919336"
	iconTwo.BackgroundTransparency = 1
	iconTwo.Position = UDim2.new(0.5, -8, 0.5, -8)
	iconTwo.SizeConstraint = Enum.SizeConstraint.RelativeXX
	iconTwo.BorderSizePixel = 0
	iconTwo.Size = UDim2.new(0, 16, 0, 16)
	iconTwo.Parent = playStop

	viewportFrame = Instance.new("ViewportFrame")
	viewportFrame.Name = "ViewportFrame"
	viewportFrame.Visible = false
	viewportFrame.BorderMode = Enum.BorderMode.Inset
	viewportFrame.LightColor = Color3.new(0.549, 0.525, 0.435)
	viewportFrame.Ambient = Color3.new(0.318, 0.318, 0.318)
	viewportFrame.Position = UDim2.new(0, 4, 0, 26)
	viewportFrame.BackgroundColor3 = Library.MainColor
	viewportFrame.BorderColor3 = Color3.new()
	viewportFrame.Size = UDim2.new(1, -8, 0, 195)
	viewportFrame.Parent = inner

	worldModel = Instance.new("WorldModel", viewportFrame)

	camera = Instance.new("Camera", viewportFrame)
	camera.CameraType = Enum.CameraType.Scriptable
	camera.FieldOfView = 70

	speedText = Instance.new("TextLabel")
	speedText.Name = "SpeedText"
	speedText.FontFace = Font.new("rbxasset://fonts/families/RobotoMono.json")
	speedText.TextColor3 = Library.FontColor
	speedText.Text = "Speed (???)"
	speedText.BackgroundTransparency = 1
	speedText.BackgroundColor3 = Color3.new(1, 1, 1)
	speedText.BorderSizePixel = 0
	speedText.BorderColor3 = Color3.new()
	speedText.TextSize = 12
	speedText.Size = UDim2.new(0, 82, 0, 20)
	speedText.ZIndex = 19
	speedText.Parent = viewportFrame

	noViewportFrame = Instance.new("Frame")
	noViewportFrame.Name = "NoViewportFrame"
	noViewportFrame.BackgroundColor3 = Library.MainColor
	noViewportFrame.Position = UDim2.new(0, 4, 0, 26)
	noViewportFrame.BorderColor3 = Color3.new()
	noViewportFrame.BorderMode = Enum.BorderMode.Inset
	noViewportFrame.Size = UDim2.new(1, -8, 0, 195)
	noViewportFrame.Parent = inner

	textLabel = Instance.new("TextLabel")
	textLabel.Name = "TextLabel"
	textLabel.FontFace = Font.new("rbxasset://fonts/families/RobotoMono.json")
	textLabel.TextColor3 = Library.FontColor
	textLabel.BorderColor3 = Color3.new()
	textLabel.Text = "Unknown Error"
	textLabel.BackgroundColor3 = Color3.new(1, 1, 1)
	textLabel.BorderSizePixel = 0
	textLabel.BackgroundTransparency = 1
	textLabel.Position = UDim2.new(0.0968, 0, 0.369, 0)
	textLabel.TextWrapped = true
	textLabel.TextSize = 14
	textLabel.Size = UDim2.new(0, 200, 0, 50)
	textLabel.Parent = noViewportFrame

	colorFrame = Instance.new("Frame")
	colorFrame.Name = "Color"
	colorFrame.BackgroundColor3 = Library.AccentColor
	colorFrame.BorderColor3 = Color3.new()
	colorFrame.BorderSizePixel = 0
	colorFrame.Size = UDim2.new(1, 0, 0, 2)
	colorFrame.Parent = inner

	frameForwards = Instance.new("TextButton")
	frameForwards.Name = "FrameForwards"
	frameForwards.FontFace = Font.new("rbxasset://fonts/families/SourceSansPro.json")
	frameForwards.TextColor3 = Color3.new()
	frameForwards.Text = ""
	frameForwards.Position = UDim2.new(0.323, 99, 0.835, -2)
	frameForwards.BackgroundColor3 = Library.MainColor
	frameForwards.BorderColor3 = Color3.new()
	frameForwards.TextSize = 14
	frameForwards.Size = UDim2.new(0, 69, 0, 20)
	frameForwards.Parent = inner

	iconThree = Instance.new("ImageLabel")
	iconThree.Name = "Icon"
	iconThree.ScaleType = Enum.ScaleType.Crop
	iconThree.BorderColor3 = Color3.new()
	iconThree.BackgroundColor3 = Library.FontColor
	iconThree.Image = "rbxassetid://10734961809"
	iconThree.BackgroundTransparency = 1
	iconThree.Position = UDim2.new(0.5, -8, 0.5, -8)
	iconThree.SizeConstraint = Enum.SizeConstraint.RelativeXX
	iconThree.BorderSizePixel = 0
	iconThree.Size = UDim2.new(0, 16, 0, 16)
	iconThree.Parent = frameForwards

	animationTextbox = Instance.new("TextBox")
	animationTextbox.Name = "AnimationTextbox"
	animationTextbox.CursorPosition = -1
	animationTextbox.TextColor3 = Library.FontColor
	animationTextbox.Text = "rbxassetid://0"
	animationTextbox.BackgroundColor3 = Library.MainColor
	animationTextbox.Position = UDim2.new(0.323, -78, 0.835, -24)
	animationTextbox.BorderColor3 = Color3.new()
	animationTextbox.FontFace = Font.new("rbxasset://fonts/families/RobotoMono.json")
	animationTextbox.TextSize = 14
	animationTextbox.Size = UDim2.new(0, 246, 0, 15)
	animationTextbox.Parent = inner

	-- Make draggable.
	Library:MakeDraggable(outer)

	-- Setup colors.
	Library:AddToRegistry(colorFrame, {
		BackgroundColor3 = "AccentColor",
	}, true)

	Library:AddToRegistry(animationVisualizerLabel, {
		TextColor3 = "AccentColor",
	}, true)

	Library:AddToRegistry(hideBorderRight, {
		BackgroundColor3 = "AccentColor",
	}, true)

	Library:AddToRegistry(sliderFill, {
		BackgroundColor3 = "AccentColor",
	}, true)

	Library:AddToRegistry(inner, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "OutlineColor",
	}, true)

	Library:AddToRegistry(playStop, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(animationTextbox, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
		TextColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(icon, {
		ImageColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(iconTwo, {
		ImageColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(iconThree, {
		ImageColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(textLabel, {
		TextColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(speedText, {
		TextColor3 = "FontColor",
	}, true)

	Library:AddToRegistry(noViewportFrame, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(frameBackwards, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(frameForwards, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(viewportFrame, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(sliderOuter, {
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(sliderInner, {
		BackgroundColor3 = "MainColor",
		BorderColor3 = "Black",
	}, true)

	Library:AddToRegistry(sliderFill, {
		BackgroundColor3 = "AccentColor",
		BorderColor3 = "AccentColorDark",
	}, true)

	Library:AddToRegistry(sliderText, {
		TextColor3 = "FontColor",
	}, true)

	-- Setup camera.
	viewportFrame.CurrentCamera = camera

	-- Setup intro scene.
	AnimationVisualizer.message("Waiting For Animation ID")

	-- Setup signals.
	visualizerMaid:mark(sliderOuter.InputBegan:Connect(onSliderInputBegan))
	visualizerMaid:mark(frameForwards.MouseButton1Click:Connect(onFrameForwards))
	visualizerMaid:mark(frameBackwards.MouseButton1Click:Connect(onFrameBackwards))
	visualizerMaid:mark(outer.InputBegan:Connect(outerFrameInputBegan))
	visualizerMaid:mark(playStop.MouseButton1Click:Connect(togglePlayStop))
	visualizerMaid:mark(runService.PreRender:Connect(onPlaybackLoop))
	visualizerMaid:mark(animationTextbox.FocusLost:Connect(onIdFocusLost))
end

---Detach AnimationVisualizer module.
function AnimationVisualizer.detach()
	visualizerMaid:clean()

	if visualizerScreenGui then
		pcall(function()
			visualizerScreenGui:Destroy()
		end)

		visualizerScreenGui = nil
	end
end

--------------------------------------------------------------------------------
-- DifferenceCalculator
--------------------------------------------------------------------------------

---@class DifferenceCalculator
DifferenceCalculator = {
	pending = nil,
	samples = {},
	lastHealth = nil,
	ui = {},
	maid = Maid.new(),
}

---@return string
local function normalizedDiffId()
	if not Options or not Options.DiffAnimationId then
		return ""
	end

	return normalizeAssetId(Options.DiffAnimationId.Value or "")
end

---Handle an entity animation for the difference calculator.
---@param entity Model
---@param track AnimationTrack
function DifferenceCalculator.onAnimation(entity, track)
	if not Toggles or not Toggles.DiffEnabled or not Toggles.DiffEnabled.Value then
		return
	end

	if not track or not track.Animation then
		return
	end

	local targetId = normalizedDiffId()

	if #targetId == 0 or normalizeAssetId(track.Animation.AnimationId) ~= targetId then
		return
	end

	DifferenceCalculator.pending = {
		at = os.clock(),
		entity = entity,
		track = track,
		keyframes = {},
	}

	pcall(function()
		for _, keyframe in next, track.Animation:GetKeyframes() do
			table.insert(DifferenceCalculator.pending.keyframes, keyframe.Time)
		end
	end)
end

---Record a damage event against the pending animation.
---@param newHealth number
function DifferenceCalculator.onHealth(newHealth)
	local last = DifferenceCalculator.lastHealth
	DifferenceCalculator.lastHealth = newHealth

	if not DifferenceCalculator.pending or not last or newHealth >= last then
		return
	end

	local window = (Options and Options.DiffMaxWindow and Options.DiffMaxWindow.Value) or 5
	local now = os.clock()
	local elapsed = now - DifferenceCalculator.pending.at

	if elapsed > window then
		DifferenceCalculator.pending = nil
		return
	end

	local sample = elapsed * 1000
	local entityName = DifferenceCalculator.pending.entity and DifferenceCalculator.pending.entity.Name or "?"
	DifferenceCalculator.pending = nil

	table.insert(DifferenceCalculator.samples, {
		ms = sample,
		entity = entityName,
		ping = Latency.rtt() * 1000,
		at = now,
	})

	if #DifferenceCalculator.samples > 50 then
		table.remove(DifferenceCalculator.samples, 1)
	end

	DifferenceCalculator.updateUI()
end

---Hook the local character's humanoid health.
---@param character Model?
local function hookLocalCharacter(character)
	if not character then
		return
	end

	local humanoid = character:WaitForChild("Humanoid", 5)

	if not humanoid then
		return
	end

	DifferenceCalculator.lastHealth = humanoid.Health

	DifferenceCalculator.maid:mark(humanoid.HealthChanged:Connect(function(health)
		DifferenceCalculator.onHealth(health)
	end))

	DifferenceCalculator.maid:mark(humanoid:GetPropertyChangedSignal("Health"):Connect(function()
		DifferenceCalculator.onHealth(humanoid.Health)
	end))
end

---Start tracking the local character.
function DifferenceCalculator.start()
	hookLocalCharacter(localPlayer and localPlayer.Character)

	DifferenceCalculator.maid:mark(localPlayer.CharacterAdded:Connect(function(character)
		DifferenceCalculator.lastHealth = nil
		hookLocalCharacter(character)
	end))
end

---Recompute and update the UI labels.
function DifferenceCalculator.updateUI()
	local ui = DifferenceCalculator.ui

	if not ui or not ui.lastLabel then
		return
	end

	local count = #DifferenceCalculator.samples

	if count == 0 then
		ui.lastLabel:SetText("Last: -")
		ui.statsLabel:SetText("Average: - | Min: - | Max: - | Count: 0")
		return
	end

	local last = DifferenceCalculator.samples[count]
	local sum, min, max = 0, math.huge, -math.huge

	for _, sample in next, DifferenceCalculator.samples do
		sum = sum + sample.ms
		min = math.min(min, sample.ms)
		max = math.max(max, sample.ms)
	end

	ui.lastLabel:SetText(string.format("Last: %.0f ms (%s, ping %.0f ms)", last.ms, last.entity, last.ping))
	ui.statsLabel:SetText(
		string.format("Average: %.0f ms | Min: %.0f ms | Max: %.0f ms | Count: %d", sum / count, min, max, count)
	)

	if ui.samplesList then
		local values = {}

		for idx = count, 1, -1 do
			local sample = DifferenceCalculator.samples[idx]
			table.insert(values, string.format("%d. %.0f ms (%s)", idx, sample.ms, sample.entity))
		end

		ui.samplesList:SetValues(values)
	end
end

---Clear all samples.
function DifferenceCalculator.clear()
	table.clear(DifferenceCalculator.samples)
	DifferenceCalculator.updateUI()
end

---Export samples to a file.
function DifferenceCalculator.export()
	local fs = FS_AVAILABLE and Filesystem.new(LOGS_FOLDER) or nil

	if not fs then
		return Logger.warn("Filesystem is unavailable; cannot export samples.")
	end

	local file = string.format("difference_%s_%d.json", tostring(placeId), os.time())

	local ok, err = pcall(function()
		fs:write(file, httpService:JSONEncode(DifferenceCalculator.samples))
	end)

	if ok then
		Logger.notify("Exported %d samples to UAPB/Logs/%s.", #DifferenceCalculator.samples, file)
	else
		Logger.warn("Failed to export samples: %s", err)
	end
end

--------------------------------------------------------------------------------
-- AutoLearn
--------------------------------------------------------------------------------

---@class AutoLearn
AutoLearn = {
	maid = Maid.new(),
	pending = {}, -- [track] = {entity, track, id, animName, startedAt, hitAt?, delayMs?, distance?}
	samples = {}, -- [id] = { delays = {}, distances = {} }
	lastHealth = nil,
	healthParent = nil, -- cached resolved parent instance holding the health value/property
	ui = { statusLabel = nil, listLabel = nil },
}

---Watched animation ids (persisted per game).
---@return string[]
function AutoLearn.ids()
	GameData.data.autoLearnIds = GameData.data.autoLearnIds or {}
	return GameData.data.autoLearnIds
end

---Write the watch list and persist.
---@param list string[]
function AutoLearn.setIds(list)
	GameData.data.autoLearnIds = list
	GameData.save()
	AutoLearn.updateListLabel()
end

---Configured HP path (persisted per game).
---@return string
function AutoLearn.healthPath()
	return GameData.data.autoLearnHealthPath or ""
end

---@param list string[]
---@return boolean
local function idInList(list, id)
	for _, watched in next, list do
		if watched == id then
			return true
		end
	end

	return false
end

---Update the "Watching: N IDs" label.
function AutoLearn.updateListLabel()
	if AutoLearn.ui.listLabel then
		AutoLearn.ui.listLabel:SetText(string.format("Watching: %d IDs", #AutoLearn.ids()))
	end
end

---Update the status label.
---@param fmt string
function AutoLearn.status(fmt, ...)
	if AutoLearn.ui.statusLabel then
		AutoLearn.ui.statusLabel:SetText("Status: " .. format(fmt, ...))
	end
end

---@param p table
local function dropPending(p)
	AutoLearn.pending[p.track] = nil
end

---Option getter with fallback.
---@param name string
---@param fallback number
---@return number
local function learnOption(name, fallback)
	return (Options and Options[name] and Options[name].Value) or fallback
end

---Read the local player's health. Blank path -> LocalPlayer Humanoid.Health, otherwise
---resolve a dotted path (PLAYERNAME substitutes the local player name). Returns nil on failure.
---@return number?
function AutoLearn.readHealth()
	local path = AutoLearn.healthPath()

	if path == "" then
		local ok, result = pcall(function()
			local character = localPlayer and localPlayer.Character

			if not character then
				return nil
			end

			local humanoid = character:FindFirstChildOfClass("Humanoid")

			return humanoid and humanoid.Health or nil
		end)

		return ok and result or nil
	end

	local root, segments = parseInstancePath(path)

	if not root or #segments == 0 then
		return nil
	end

	-- Re-resolve the cached parent when it is missing or was destroyed (respawn).
	if not AutoLearn.healthParent or AutoLearn.healthParent.Parent == nil then
		local resolved = nil

		pcall(function()
			local current = root

			for index = 1, #segments - 1 do
				if not current then
					return
				end

				current = current:FindFirstChild(segments[index])
			end

			resolved = current
		end)

		AutoLearn.healthParent = resolved
	end

	local parent = AutoLearn.healthParent

	if not parent then
		return nil
	end

	local last = segments[#segments]

	local ok, result = pcall(function()
		local target = parent:FindFirstChild(last)

		if target and target:IsA("ValueBase") then
			return target.Value
		end

		local value = parent[last]

		if type(value) == "number" then
			return value
		end

		return nil
	end)

	return ok and result or nil
end

---Commit a learned sample into a timing.
---@param p table
function AutoLearn.commit(p)
	local samples = AutoLearn.samples[p.id]

	if not samples then
		samples = { delays = {}, distances = {} }
		AutoLearn.samples[p.id] = samples
	end

	table.insert(samples.delays, p.delayMs)

	if p.distance then
		table.insert(samples.distances, p.distance)
	end

	local sum, count = 0, 0

	for _, delay in next, samples.delays do
		sum = sum + delay
		count = count + 1
	end

	local avgDelay = math.floor(sum / math.max(count, 1) + 0.5)
	local maxDist = 0

	for _, distance in next, samples.distances do
		maxDist = math.max(maxDist, distance)
	end

	local size = maxDist + learnOption("AutoLearnPadding", 1)
	local container = config:get().animation
	local timing = container:index(p.id)
	local updateExisting = Toggles and Toggles.AutoLearnUpdateExisting and Toggles.AutoLearnUpdateExisting.Value

	if not timing then
		local name = p.animName ~= "" and p.animName or p.id

		if container:find(name) then
			name = string.format("%s (%s)", name, p.id)
		end

		timing = AnimationTiming.new({ _id = p.id })
		timing.name = name
		timing.fhb = true
		timing.hitbox = Vector3.new(size, size, size)

		local ok, err = timing.actions:push(Action.new({
			_type = "Parry",
			name = "Parry",
			_when = avgDelay,
		}))

		if not ok then
			AutoLearn.status("failed: %s", err)
			return Logger.warn("Auto Learn action push failed: %s", err)
		end

		local pushed, pushErr = container:push(timing)

		if not pushed then
			AutoLearn.status("failed: %s", pushErr)
			return Logger.warn("Auto Learn timing push failed: %s", pushErr)
		end
	elseif updateExisting then
		timing.hitbox = Vector3.new(size, size, size)
		timing.fhb = true

		local target = nil

		for _, action in next, timing.actions:sorted() do
			if action._type == "Parry" then
				target = action
				break
			end
		end

		target = target or timing.actions:sorted()[1]

		if target then
			target._when = avgDelay
		end
	else
		AutoLearn.status("'%s' recorded sample only (update disabled)", p.animName)
	end

	TimingStore.markDirty()

	if refreshAllSections then
		refreshAllSections()
	end

	Logger.notify("Auto Learn hit: %s -> delay %d ms, hitbox %.1f (n=%d)", p.animName, avgDelay, size, count)
	AutoLearn.status("'%s' hit -> %d ms, hitbox %.1f (n=%d)", p.animName, avgDelay, size, count)
end

---Handle an entity animation for auto learning.
---@param entity Model
---@param track AnimationTrack
function AutoLearn.onAnimation(entity, track)
	if not (Toggles and Toggles.AutoLearnEnabled and Toggles.AutoLearnEnabled.Value) then
		return
	end

	if not track or not track.Animation then
		return
	end

	if entity == (localPlayer and localPlayer.Character) then
		return
	end

	local id = normalizeAssetId(track.Animation.AnimationId)

	if not idInList(AutoLearn.ids(), id) then
		return
	end

	local p = {
		entity = entity,
		track = track,
		id = id,
		animName = track.Animation.Name,
		startedAt = os.clock(),
	}

	AutoLearn.pending[track] = p

	-- Keep the pending alive for the whole damage window: the hit can land after
	-- the animation track has already stopped.
	task.delay(learnOption("AutoLearnDamageWindow", 2000) / 1000 + 0.1, function()
		if AutoLearn.pending[track] == p then
			dropPending(p)
			AutoLearn.status("'%s' - no HP change within window", p.animName)
		end
	end)
end

---Called when the polled HP changes; commits the most recent qualifying pending.
function AutoLearn.onHealthChanged()
	local now = os.clock()
	local damageWindow = learnOption("AutoLearnDamageWindow", 2000)
	local best = nil

	for _, p in next, AutoLearn.pending do
		if p.hitAt or now - p.startedAt > damageWindow / 1000 then
			continue
		end

		local distance = entityDistance(p.entity)

		if distance == nil then
			continue
		end

		if not best or p.startedAt > best.startedAt then
			best = p
		end
	end

	if not best then
		return
	end

	best.hitAt = now
	best.delayMs = math.floor((now - best.startedAt) * 1000 + 0.5)
	best.distance = entityDistance(best.entity)

	dropPending(best)
	AutoLearn.commit(best)
end

---Start polling the local player's HP.
function AutoLearn.start()
	AutoLearn.maid:mark(runService.Heartbeat:Connect(function()
		if UNLOADED then
			return
		end

		if not (Toggles and Toggles.AutoLearnEnabled and Toggles.AutoLearnEnabled.Value) then
			return
		end

		local health = AutoLearn.readHealth()
		local last = AutoLearn.lastHealth
		AutoLearn.lastHealth = health

		if health == nil or last == nil then
			-- Respawn / unreadable: next valid read must not register as a change.
			return
		end

		local changed = health ~= last
		local anyChange = Toggles and Toggles.AutoLearnAnyChange and Toggles.AutoLearnAnyChange.Value

		if changed and (anyChange or health < last) then
			AutoLearn.onHealthChanged()
		end
	end))
end

---Stop auto learning.
function AutoLearn.stop()
	for _, p in next, AutoLearn.pending do
		dropPending(p)
	end

	AutoLearn.lastHealth = nil
	AutoLearn.healthParent = nil
	AutoLearn.maid:clean()
end

--------------------------------------------------------------------------------
-- Defense
--------------------------------------------------------------------------------

---@class Defense
Defense = {
	states = {}, -- entity -> { generation }
	lastTriggered = nil,
}

---@param entity Model
---@return table
local function entityState(entity)
	local state = Defense.states[entity]

	if not state then
		state = { generation = 0 }
		Defense.states[entity] = state
	end

	return state
end

---Execute a single action.
---@param action Action
---@param timing Timing
---@param entity Model?
function Defense.execute(action, timing, entity)
	local actionType = action._type

	if actionType == "Parry" then
		local onCooldown = os.clock() - Input.lastParryAt
			< ((Options and Options.ParryCooldown and Options.ParryCooldown.Value) or 0.25)

		if
			onCooldown
			and Toggles
			and Toggles.UseDodgeFallback
			and Toggles.UseDodgeFallback.Value
			and not timing.ndfb
		then
			Input.dodge()
		else
			Input.parry()
		end
	elseif actionType == "Dodge" then
		Input.dodge()
	elseif actionType == "Jump" then
		Input.jump()
	elseif actionType == "Start Block" then
		Input.block(true)
	elseif actionType == "End Block" then
		Input.block(false)
	elseif actionType == "Custom Key" then
		task.spawn(Input.pressKey, action.key or "F")
	elseif actionType == "Remote" then
		local template = action.remote and GameDataRemotes()[action.remote]

		if action.remote and GameDataRemotesDisabled()[action.remote] then
			template = nil
		end

		if template then
			RemoteResolver.fire(template)
		else
			Logger.warn("Remote action references unknown template '%s'.", tostring(action.remote))
		end
	end

	local isRepeat = Defense.lastTriggered and Defense.lastTriggered.timing == timing

	Defense.lastTriggered = {
		timing = timing,
		entity = entity,
		at = os.clock(),
	}

	if Toggles and Toggles.NotifyDefense and Toggles.NotifyDefense.Value then
		if not (timing.srpn and isRepeat) then
			Library:Notify(string.format("%s %s (%s)", actionType, timing.name, entity and entity.Name or "?"))
		end
	end
end

---Validate whether a hitbox check passes for an action.
---@param action Action
---@param timing Timing
---@param entityRoot BasePart
---@return boolean
function Defense.hitboxPasses(action, timing, entityRoot)
	if action.ihbc then
		return true
	end

	local localRoot = Input.localRoot()

	if not localRoot or not entityRoot then
		return false
	end

	local size = Hitbox.effectiveSize(action, timing)
	local visualize = Toggles and Toggles.VisualizeHitboxes and Toggles.VisualizeHitboxes.Value

	return Hitbox.check(entityRoot, localRoot, size, timing.fhb, timing.hso, visualize)
end

---Dispatch a timing for an entity.
---@param entity Model?
---@param root BasePart
---@param timing Timing
---@param track AnimationTrack?
function Defense.dispatch(entity, root, timing, track)
	if UNLOADED then
		return
	end

	if not Toggles or not Toggles.EnableAutoDefense or not Toggles.EnableAutoDefense.Value then
		return
	end

	local localRoot = Input.localRoot()

	if not localRoot or not root then
		return
	end

	local distance = (localRoot.Position - root.Position).Magnitude

	if distance < timing.imdd or distance > timing.imxd then
		return
	end

	local state = entity and entityState(entity) or { generation = 0 }
	state.generation = state.generation + 1
	local generation = state.generation

	local latencyComp = (Toggles and Toggles.CompensatePing and Toggles.CompensatePing.Value) and (Latency.rtt() / 2)
		or 0

	---Is this dispatch still current and the track still playing?
	---@return boolean
	local function alive()
		if UNLOADED or state.generation ~= generation then
			return false
		end

		if track and not timing.iae and not track.IsPlaying then
			return false
		end

		return true
	end

	if timing.rpue then
		-- Repeat-until-end mode: loop every _rpd ms after _rsd until the track stops or mat expires.
		task.delay(timing:rsd(), function()
			local started = os.clock()
			local mat = (timing.mat or 2000) / 1000
			local period = math.max(timing:rpd(), 0.05)

			while alive() and (os.clock() - started) < mat do
				local action = timing.actions:sorted()[1]

				if action and Defense.hitboxPasses(action, timing, root) then
					Defense.execute(action, timing, entity)
				end

				task.wait(period)
			end
		end)

		return
	end

	for _, scheduled in next, timing.actions:sorted() do
		local delay = math.max(0, scheduled:when() - latencyComp)

		task.delay(delay, function()
			if not alive() then
				return
			end

			-- Re-fetch the live action so builder edits apply in real time.
			local action = timing.actions:find(scheduled.name)

			if not action then
				return
			end

			if action.ihbc then
				Defense.execute(action, timing, entity)
				return
			end

			if timing.duih then
				-- Poll every Heartbeat until inside the hitbox or the timeout elapses.
				local timeout = (Options and Options.DuihTimeout and Options.DuihTimeout.Value) or 1.5
				local started = os.clock()

				while alive() and (os.clock() - started) < timeout do
					if Defense.hitboxPasses(action, timing, root) then
						Defense.execute(action, timing, entity)
						return
					end

					runService.Heartbeat:Wait()
				end

				return
			end

			if Defense.hitboxPasses(action, timing, root) then
				Defense.execute(action, timing, entity)
			end
		end)
	end
end

---Handle a played animation.
---@param entity Model
---@param track AnimationTrack
function Defense.onAnimation(entity, track)
	if not track or not track.Animation then
		return
	end

	local distance = entityDistance(entity)
	local timing = config:get().animation:index(normalizeAssetId(track.Animation.AnimationId))

	if not timing then
		InfoLogger.miss(
			"Animation",
			tostring(track.Animation.AnimationId),
			track.Animation.Name,
			distance,
			entity and entity.Name or nil
		)
		return
	end

	local root = entity and entityRoot(entity)

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing, track)
end

---Handle a descendant added to an entity (effect timings).
---@param entity Model
---@param inst Instance
function Defense.onEffect(entity, inst)
	local distance = entityDistance(entity)
	local timing = config:get().effect:index(inst.Name)

	if not timing then
		InfoLogger.miss("Effect", inst.Name, nil, distance, entity and entity.Name or nil)
		return
	end

	local root = entity and entityRoot(entity)

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing)
end

---Handle a sound that started playing on an entity.
---@param entity Model
---@param sound Sound
function Defense.onSound(entity, sound)
	local distance = entityDistance(entity)
	local timing = config:get().sound:index(normalizeAssetId(sound.SoundId))

	if not timing then
		InfoLogger.miss("Sound", tostring(sound.SoundId), sound.Name, distance, entity and entity.Name or nil)
		return
	end

	local root = entity and entityRoot(entity)

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing)
end

---Handle a BasePart added to workspace (part timings).
---@param part BasePart
function Defense.onPart(part)
	local distance = nil
	local localRoot = Input.localRoot()

	if localRoot then
		distance = (localRoot.Position - part.Position).Magnitude
	end

	local timing = config:get().part:index(part.Name)

	if not timing then
		InfoLogger.miss("Part", part.Name, nil, distance, part.Parent and part.Parent.Name or nil)
		return
	end

	if timing.pparent and #timing.pparent > 0 then
		local parent = part.Parent
		local matches = false

		while parent do
			if parent.Name == timing.pparent then
				matches = true
				break
			end

			parent = parent.Parent
		end

		if not matches then
			return
		end
	end

	-- Validate using the part itself as the entity root.
	Defense.dispatch(Entities.nearest(part.Position), part, timing)
end

--------------------------------------------------------------------------------
-- Hitbox Simulation (builder tool)
--------------------------------------------------------------------------------

local Simulation = {
	maid = Maid.new(),
	part = nil,
}

---One simulation step: draw a hitbox around the local player and color it by detected entities.
function Simulation.step()
	local toggle = Toggles and Toggles.ShowHitboxSimulation

	if not Options or not toggle or not toggle.Value then
		Simulation.clear()
		return
	end

	local character = localPlayer and localPlayer.Character
	local root = character and character:FindFirstChild("HumanoidRootPart")

	if not root then
		return
	end

	local shape = (Options.HS_HitboxType and Options.HS_HitboxType.Value) or "Block"
	local size = Vector3.new(
		(Options.HS_HitboxSizeX and Options.HS_HitboxSizeX.Value) or 4,
		(Options.HS_HitboxSizeY and Options.HS_HitboxSizeY.Value) or 4,
		(Options.HS_HitboxSizeZ and Options.HS_HitboxSizeZ.Value) or 4
	)

	local usedCFrame = root.CFrame

	if Toggles.HS_FacingOffset and Toggles.HS_FacingOffset.Value then
		usedCFrame = usedCFrame * CFrame.new(0, 0, -size.Z / 2)
	end

	local shift = (Options.HS_ShiftOffset and Options.HS_ShiftOffset.Value) or 0

	if shift ~= 0 then
		usedCFrame = usedCFrame * CFrame.new(0, 0, shift)
	end

	local part = Simulation.part

	if not part then
		part = Instance.new("Part")
		part.Name = "UAPB_SimulationPart"
		part.Anchored = true
		part.CanCollide = false
		part.CanQuery = false
		part.CanTouch = false
		part.Material = Enum.Material.ForceField
		part.CastShadow = false
		part.Transparency = 0.5
		part.Parent = workspace
		Simulation.part = part
	end

	part.Size = size
	part.CFrame = usedCFrame

	if shape == "Ball" then
		part.Shape = Enum.PartType.Ball
	elseif shape == "Cylinder" then
		part.Shape = Enum.PartType.Cylinder
		part.CFrame = usedCFrame * CFrame.Angles(0, 0, math.rad(90))
	else
		part.Shape = Enum.PartType.Block
	end

	-- Detection: all humanoid models in workspace except the local character.
	local instances = {}

	for model in next, Entities.tracked do
		if model ~= character and model:IsDescendantOf(workspace) then
			table.insert(instances, model)
		end
	end

	local overlap = OverlapParams.new()
	overlap.FilterDescendantsInstances = instances
	overlap.FilterType = Enum.RaycastFilterType.Include

	local parts = workspace:GetPartsInPart(part, overlap)
	part.Color = #parts > 0 and Color3.fromRGB(0, 255, 0) or Color3.fromRGB(255, 0, 0)
end

---Remove the simulation part.
function Simulation.clear()
	if Simulation.part then
		pcall(function()
			Simulation.part:Destroy()
		end)

		Simulation.part = nil
	end
end

--------------------------------------------------------------------------------
-- Utility helpers used by the UI
--------------------------------------------------------------------------------

local BuilderSections = {} -- kind -> BuilderSection

---@return string[]
local function remoteTemplateNames()
	local names = {}

	for name in next, GameDataRemotes() do
		if name ~= "Parry" and name ~= "Dodge" and name ~= "Start Block" and name ~= "End Block" then
			table.insert(names, name)
		end
	end

	table.sort(names)
	return names
end

---Refresh every builder action-remote dropdown.
local function refreshRemoteDropdowns()
	local names = remoteTemplateNames()

	for _, section in next, BuilderSections do
		if section.actionRemote then
			section.actionRemote:SetValues(names)
		end
	end
end

--------------------------------------------------------------------------------
-- UI (Linoria)
--------------------------------------------------------------------------------

local LINORIA_BASE = "https://raw.githubusercontent.com/violin-suzutsuki/LinoriaLib/main/"
local ThemeManager
local SaveManager
local Window

---Load the Linoria library and addons.
---@return boolean
local function loadLibraries()
	local ok, lib = pcall(function()
		return loadstringFn(game:HttpGet(LINORIA_BASE .. "Library.lua"))()
	end)

	if not ok or not lib then
		Logger.warn("Failed to load Linoria library: %s", tostring(lib))
		return false
	end

	Library = lib

	pcall(function()
		ThemeManager = loadstringFn(game:HttpGet(LINORIA_BASE .. "addons/ThemeManager.lua"))()
	end)

	pcall(function()
		SaveManager = loadstringFn(game:HttpGet(LINORIA_BASE .. "addons/SaveManager.lua"))()
	end)

	Toggles = getgenvSafe().Toggles
	Options = getgenvSafe().Options

	return Toggles ~= nil and Options ~= nil
end

--------------------------------------------------------------------------------
-- BuilderSection
--------------------------------------------------------------------------------

---@class BuilderSection
---@note: We assume that all elements will exist in callbacks.
---@field kind string
---@field container TimingContainer
---@field module table
---@field loading boolean
local BuilderSection = {}
BuilderSection.__index = BuilderSection

local KIND_LABELS = {
	animation = "Animation",
	sound = "Sound",
	part = "Part",
	effect = "Effect",
}

---@param kind string
---@return string
local function bid(kind, name)
	return "B_" .. KIND_LABELS[kind] .. "_" .. name
end

---Wrap a callback that needs a selected timing. Marks the store dirty afterwards.
---@param callback function
---@return function
function BuilderSection:tnc(callback)
	return function(...)
		if self.loading then
			return
		end

		if not self.timingList.Value then
			return Logger.warn("No timing selected.")
		end

		local timing = self.container:find(self.timingList.Value)

		if not timing then
			return Logger.longNotify("You must select a valid timing to perform this action.")
		end

		callback(timing, ...)
		TimingStore.markDirty()
	end
end

---Wrap a callback that needs a selected action.
---@param callback function
---@return function
function BuilderSection:anc(callback)
	return function(...)
		if self.loading then
			return
		end

		if not self.timingList.Value then
			return Logger.warn("No timing selected.")
		end

		local timing = self.container:find(self.timingList.Value)

		if not timing then
			return Logger.longNotify("You must select a valid timing to perform this action.")
		end

		if not self.actionList.Value then
			return Logger.warn("No action selected.")
		end

		local action = timing.actions:find(self.actionList.Value)

		if not action then
			return Logger.longNotify("You must select a valid action to perform this action.")
		end

		callback(action, ...)
		TimingStore.markDirty()
	end
end

---Wrap a callback that needs both a timing and an action.
---@param callback function
---@return function
function BuilderSection:tanc(callback)
	return function(...)
		if self.loading then
			return
		end

		if not self.timingList.Value then
			return Logger.warn("No timing selected.")
		end

		local timing = self.container:find(self.timingList.Value)

		if not timing then
			return Logger.longNotify("You must select a valid timing to perform this action.")
		end

		if not self.actionList.Value then
			return Logger.warn("No action selected.")
		end

		local action = timing.actions:find(self.actionList.Value)

		if not action then
			return Logger.longNotify("You must select a valid action to perform this action.")
		end

		callback(timing, action, ...)
		TimingStore.markDirty()
	end
end

---Refresh the timing list dropdown.
function BuilderSection:refresh()
	self.timingList:SetValues(self.container:names())
	self.timingList:SetValue(nil)
end

---Refresh the action list dropdown.
---@param timing Timing?
function BuilderSection:arefresh(timing)
	self.actionList:SetValues(timing and timing.actions:names() or {})
	self.actionList:SetValue(nil)
end

---Reset the timing elements to defaults.
function BuilderSection:reset()
	self.loading = true

	self.timingName:SetValue("")
	self.timingId:SetValue("")
	self.timingTag:SetValue("Undefined")
	self.timingImdd:SetValue(0)
	self.timingImxd:SetValue(1000)
	self.timingPunishable:SetValue(0.6)
	self.timingAfter:SetValue(0.1)
	self.timingBfht:SetValue(0.3)
	self.timingHso:SetValue(0)
	self.timingFhb:SetValue(true)
	self.timingDuih:SetValue(false)
	self.timingHitboxW:SetValue(0)
	self.timingHitboxH:SetValue(0)
	self.timingHitboxL:SetValue(0)
	self.timingNdfb:SetValue(false)
	self.timingNbfb:SetValue(false)
	self.timingRpue:SetValue(false)
	self.timingRsd:SetValue(0)
	self.timingRpd:SetValue(0)
	self.timingSrpn:SetValue(false)

	if self.kind == "animation" then
		self.animHa:SetValue(false)
		self.animIae:SetValue(false)
		self.animIeae:SetValue(false)
		self.animMat:SetValue(2000)
		self.animPhd:SetValue(false)
		self.animPhds:SetValue(0)
		self.animPfh:SetValue(false)
		self.animPfht:SetValue(0.15)
		self.animDp:SetValue(false)
	elseif self.kind == "part" then
		self.partPparent:SetValue("")
	end

	self:arefresh(nil)
	self:raction()

	self.loading = false
end

---Reset the action elements.
function BuilderSection:raction()
	self.actionName:SetValue("")
	self.actionType:SetValue("Parry")
	self.actionDelay:SetValue(0)
	self.actionHitboxW:SetValue(0)
	self.actionHitboxH:SetValue(0)
	self.actionHitboxL:SetValue(0)
	self.actionIhbc:SetValue(false)
	self.actionKey:SetValue("")
	self.actionRemote:SetValue(nil)
end

---Load a timing's values into the elements.
---@param timing Timing
function BuilderSection:loadTiming(timing)
	self.loading = true

	self.timingName:SetValue(timing.name)
	self.timingTag:SetValue(timing.tag)
	self.timingImdd:SetValue(timing.imdd)
	self.timingImxd:SetValue(timing.imxd)
	self.timingPunishable:SetValue(timing.punishable)
	self.timingAfter:SetValue(timing.after)
	self.timingBfht:SetValue(timing.bfht)
	self.timingHso:SetValue(timing.hso)
	self.timingFhb:SetValue(timing.fhb)
	self.timingDuih:SetValue(timing.duih)
	self.timingHitboxW:SetValue(timing.hitbox.X)
	self.timingHitboxH:SetValue(timing.hitbox.Y)
	self.timingHitboxL:SetValue(timing.hitbox.Z)
	self.timingNdfb:SetValue(timing.ndfb)
	self.timingNbfb:SetValue(timing.nbfb)
	self.timingRpue:SetValue(timing.rpue)
	self.timingRsd:SetValue(timing._rsd)
	self.timingRpd:SetValue(timing._rpd)
	self.timingSrpn:SetValue(timing.srpn)

	if self.kind == "animation" then
		self.timingId:SetValue(timing._id)
		self.animHa:SetValue(timing.ha)
		self.animIae:SetValue(timing.iae)
		self.animIeae:SetValue(timing.ieae)
		self.animMat:SetValue(timing.mat)
		self.animPhd:SetValue(timing.phd)
		self.animPhds:SetValue(timing.phds)
		self.animPfh:SetValue(timing.pfh)
		self.animPfht:SetValue(timing.pfht)
		self.animDp:SetValue(timing.dp)
	elseif self.kind == "sound" then
		self.timingId:SetValue(timing._id)
	elseif self.kind == "part" then
		self.timingId:SetValue(timing.pname)
		self.partPparent:SetValue(timing.pparent or "")
	elseif self.kind == "effect" then
		self.timingId:SetValue(timing.ename)
	end

	self:arefresh(timing)
	self:raction()

	self.loading = false
end

---Load an action's values into the elements.
---@param action Action
function BuilderSection:loadAction(action)
	self.loading = true

	self.actionName:SetValue(action.name)
	self.actionType:SetValue(action._type)
	self.actionDelay:SetValue(action._when)
	self.actionHitboxW:SetValue(action.hitbox.X)
	self.actionHitboxH:SetValue(action.hitbox.Y)
	self.actionHitboxL:SetValue(action.hitbox.Z)
	self.actionIhbc:SetValue(action.ihbc)
	self.actionKey:SetValue(action.key or "")
	self.actionRemote:SetValue(action.remote)

	self.loading = false
end

---Validate fields before creating a timing.
---@return boolean
function BuilderSection:check()
	if not self.timingName.Value or #self.timingName.Value == 0 then
		return Logger.longNotify("Please enter a valid timing name.")
	end

	if self.container:find(self.timingName.Value) then
		return Logger.longNotify("The timing '%s' already exists in the list.", self.timingName.Value)
	end

	if not self.timingId.Value or #self.timingId.Value == 0 then
		return Logger.longNotify("Please enter a valid timing identifier.")
	end

	if self.kind == "part" and self.container:index(self.timingId.Value) then
		return Logger.longNotify("A timing for '%s' already exists.", self.timingId.Value)
	end

	if
		(self.kind == "animation" or self.kind == "sound")
		and self.container:index(normalizeAssetId(self.timingId.Value))
	then
		return Logger.longNotify("A timing for '%s' already exists.", self.timingId.Value)
	end

	if self.kind == "effect" and self.container:index(self.timingId.Value) then
		return Logger.longNotify("A timing for '%s' already exists.", self.timingId.Value)
	end

	return true
end

---Set kind-specific fields on a new timing.
---@param timing Timing
function BuilderSection:cset(timing)
	timing.name = self.timingName.Value

	if self.kind == "animation" or self.kind == "sound" then
		timing._id = normalizeAssetId(self.timingId.Value)
	elseif self.kind == "part" then
		timing.pname = self.timingId.Value
	elseif self.kind == "effect" then
		timing.ename = self.timingId.Value
	end
end

---Create a new timing of this kind.
---@return Timing
function BuilderSection:create()
	local timing = self.module.new()
	self:cset(timing)
	return timing
end

---Validate before creating an action.
---@param timing Timing
---@return boolean
function BuilderSection:acheck(timing)
	if not self.actionName.Value or #self.actionName.Value == 0 then
		return Logger.longNotify("Please enter a valid action name.")
	end

	if timing.actions:find(self.actionName.Value) then
		return Logger.longNotify("The action '%s' already exists in the list.", self.actionName.Value)
	end

	return true
end

---Build all elements into a tabbox tab.
---@param tab table
function BuilderSection:build(tab)
	local kind = self.kind
	local idLabel = ({ animation = "Animation ID", sound = "Sound ID", part = "Part Name", effect = "Effect Name" })[kind]

	self.timingList = tab:AddDropdown(bid(kind, "TimingList"), {
		Text = "Timing List",
		Values = self.container:names(),
		AllowNull = true,
		Callback = function(value)
			if self.loading or not value then
				return
			end

			local timing = self.container:find(value)

			if timing then
				self:loadTiming(timing)
			end
		end,
	})

	self.timingName = tab:AddInput(bid(kind, "TimingName"), {
		Text = "Timing Name",
	})

	self.timingId = tab:AddInput(bid(kind, "TimingId"), {
		Text = idLabel,
	})

	tab:AddButton({
		Text = "Create Timing",
		Func = function()
			if not self:check() then
				return
			end

			local timing = self:create()
			local ok, err = self.container:push(timing)

			if not ok then
				return Logger.longNotify(err)
			end

			TimingStore.markDirty()
			self:refresh()
			self.timingList:SetValue(timing.name)
		end,
	})

	tab:AddButton({
		Text = "Duplicate Timing",
		Func = function()
			if not self.timingList.Value then
				return Logger.warn("No timing selected.")
			end

			local timing = self.container:find(self.timingList.Value)

			if not timing then
				return
			end

			local clone = timing:clone()
			local name = timing.name .. " copy"
			local counter = 1

			while self.container:find(name) do
				counter = counter + 1
				name = timing.name .. " copy " .. counter
			end

			clone.name = name

			local ok, err = self.container:push(clone)

			if not ok then
				return Logger.longNotify(err)
			end

			TimingStore.markDirty()
			self:refresh()
		end,
	})

	tab:AddButton({
		Text = "Remove Timing",
		Func = function()
			if not self.timingList.Value then
				return Logger.warn("No timing selected.")
			end

			local timing = self.container:find(self.timingList.Value)

			if not timing then
				return
			end

			self.container:remove(timing)
			TimingStore.markDirty()
			self:refresh()
			self:reset()
		end,
	})

	tab:AddDivider()

	-- Timing fields.
	self.timingTag = tab:AddDropdown(bid(kind, "TimingTag"), {
		Text = "Tag",
		Values = TIMING_TAGS,
		Default = "Undefined",
		Callback = self:tnc(function(timing, value)
			timing.tag = value
		end),
	})

	self.timingImdd = tab:AddSlider(bid(kind, "Imdd"), {
		Text = "Minimum Distance",
		Min = 0,
		Max = 1000,
		Default = 0,
		Rounding = 0,
		Callback = self:tnc(function(timing, value)
			timing.imdd = value
		end),
	})

	self.timingImxd = tab:AddSlider(bid(kind, "Imxd"), {
		Text = "Maximum Distance",
		Min = 0,
		Max = 1000,
		Default = 1000,
		Rounding = 0,
		Callback = self:tnc(function(timing, value)
			timing.imxd = value
		end),
	})

	self.timingPunishable = tab:AddSlider(bid(kind, "Punishable"), {
		Text = "Punishable Window",
		Min = 0,
		Max = 5,
		Default = 0.6,
		Rounding = 2,
		Callback = self:tnc(function(timing, value)
			timing.punishable = value
		end),
	})

	self.timingAfter = tab:AddSlider(bid(kind, "After"), {
		Text = "After Window",
		Min = 0,
		Max = 5,
		Default = 0.1,
		Rounding = 2,
		Callback = self:tnc(function(timing, value)
			timing.after = value
		end),
	})

	self.timingBfht = tab:AddSlider(bid(kind, "Bfht"), {
		Text = "Block Fallback Hold Time",
		Min = 0,
		Max = 5,
		Default = 0.3,
		Rounding = 2,
		Callback = self:tnc(function(timing, value)
			timing.bfht = value
		end),
	})

	self.timingHso = tab:AddSlider(bid(kind, "Hso"), {
		Text = "Hitbox Shift Offset",
		Min = -10,
		Max = 10,
		Default = 0,
		Rounding = 1,
		Callback = self:tnc(function(timing, value)
			timing.hso = value
		end),
	})

	self.timingFhb = tab:AddToggle(bid(kind, "Fhb"), {
		Text = "Hitbox Facing Offset",
		Default = true,
		Callback = self:tnc(function(timing, value)
			timing.fhb = value
		end),
	})

	self.timingDuih = tab:AddToggle(bid(kind, "Duih"), {
		Text = "Delay Until In Hitbox",
		Default = false,
		Callback = self:tnc(function(timing, value)
			timing.duih = value
		end),
	})

	self.timingHitboxW = tab:AddSlider(bid(kind, "HitboxW"), {
		Text = "Timing Hitbox Width",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:tnc(function(timing, value)
			timing.hitbox = Vector3.new(value, timing.hitbox.Y, timing.hitbox.Z)
		end),
	})

	self.timingHitboxH = tab:AddSlider(bid(kind, "HitboxH"), {
		Text = "Timing Hitbox Height",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:tnc(function(timing, value)
			timing.hitbox = Vector3.new(timing.hitbox.X, value, timing.hitbox.Z)
		end),
	})

	self.timingHitboxL = tab:AddSlider(bid(kind, "HitboxL"), {
		Text = "Timing Hitbox Length",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:tnc(function(timing, value)
			timing.hitbox = Vector3.new(timing.hitbox.X, timing.hitbox.Y, value)
		end),
	})

	self.timingNdfb = tab:AddToggle(bid(kind, "Ndfb"), {
		Text = "No Dodge Fallback",
		Default = false,
		Callback = self:tnc(function(timing, value)
			timing.ndfb = value
		end),
	})

	self.timingNbfb = tab:AddToggle(bid(kind, "Nbfb"), {
		Text = "No Block Fallback",
		Default = false,
		Callback = self:tnc(function(timing, value)
			timing.nbfb = value
		end),
	})

	self.timingSrpn = tab:AddToggle(bid(kind, "Srpn"), {
		Text = "Skip Repeat Notification",
		Default = false,
		Callback = self:tnc(function(timing, value)
			timing.srpn = value
		end),
	})

	self.timingRpue = tab:AddToggle(bid(kind, "Rpue"), {
		Text = "Repeat Until End",
		Default = false,
		Callback = self:tnc(function(timing, value)
			timing.rpue = value
		end),
	})

	local repeatBox = tab:AddDependencyBox()

	self.timingRsd = repeatBox:AddInput(bid(kind, "Rsd"), {
		Text = "Repeat Start Delay (ms)",
		Numeric = true,
		Finished = true,
		Callback = self:tnc(function(timing, value)
			timing._rsd = tonumber(value) or 0
		end),
	})

	self.timingRpd = repeatBox:AddInput(bid(kind, "Rpd"), {
		Text = "Repeat Delay (ms)",
		Numeric = true,
		Finished = true,
		Callback = self:tnc(function(timing, value)
			timing._rpd = tonumber(value) or 0
		end),
	})

	repeatBox:SetupDependencies({
		{ self.timingRpue, true },
	})

	-- Kind-specific extras.
	if kind == "animation" then
		self.animHa = tab:AddToggle(bid(kind, "Ha"), {
			Text = "Cancellable By Hit",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.ha = value
			end),
		})

		self.animIae = tab:AddToggle(bid(kind, "Iae"), {
			Text = "Ignore Animation End",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.iae = value
			end),
		})

		self.animIeae = tab:AddToggle(bid(kind, "Ieae"), {
			Text = "Ignore Early Animation End",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.ieae = value
			end),
		})

		self.animMat = tab:AddInput(bid(kind, "Mat"), {
			Text = "Max Animation Timeout (ms)",
			Numeric = true,
			Finished = true,
			Callback = self:tnc(function(timing, value)
				timing.mat = tonumber(value) or 2000
			end),
		})

		self.animPhd = tab:AddToggle(bid(kind, "Phd"), {
			Text = "Past Hitbox Detection",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.phd = value
			end),
		})

		self.animPhds = tab:AddSlider(bid(kind, "Phds"), {
			Text = "Past Hitbox History (s)",
			Min = 0,
			Max = 5,
			Default = 0,
			Rounding = 2,
			Callback = self:tnc(function(timing, value)
				timing.phds = value
			end),
		})

		self.animPfh = tab:AddToggle(bid(kind, "Pfh"), {
			Text = "Predict Hitbox Facing",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.pfh = value
			end),
		})

		self.animPfht = tab:AddSlider(bid(kind, "Pfht"), {
			Text = "Hitbox Prediction Time (s)",
			Min = 0,
			Max = 2,
			Default = 0.15,
			Rounding = 2,
			Callback = self:tnc(function(timing, value)
				timing.pfht = value
			end),
		})

		self.animDp = tab:AddToggle(bid(kind, "Dp"), {
			Text = "Disable Prediction",
			Default = false,
			Callback = self:tnc(function(timing, value)
				timing.dp = value
			end),
		})
	elseif kind == "part" then
		self.partPparent = tab:AddInput(bid(kind, "Pparent"), {
			Text = "Parent Name Filter",
			Callback = self:tnc(function(timing, value)
				timing.pparent = value
			end),
		})
	end

	tab:AddDivider()

	-- Action fields.
	self.actionList = tab:AddDropdown(bid(kind, "ActionList"), {
		Text = "Action List",
		Values = {},
		AllowNull = true,
		Callback = function(value)
			if self.loading or not self.timingList.Value or not value then
				return
			end

			local timing = self.container:find(self.timingList.Value)

			if not timing then
				return
			end

			local action = timing.actions:find(value)

			if action then
				self:loadAction(action)
			end
		end,
	})

	self.actionType = tab:AddDropdown(bid(kind, "ActionType"), {
		Text = "Action Type",
		Values = ACTION_TYPES,
		Default = "Parry",
		Callback = self:anc(function(action, value)
			action._type = value
		end),
	})

	self.actionDelay = tab:AddInput(bid(kind, "ActionDelay"), {
		Text = "Action Delay (ms)",
		Numeric = true,
		Finished = true,
		Callback = self:anc(function(action, value)
			action._when = tonumber(value) or 0
		end),
	})

	self.actionHitboxW = tab:AddSlider(bid(kind, "ActionHitboxW"), {
		Text = "Action Hitbox Width",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:anc(function(action, value)
			action.hitbox = Vector3.new(value, action.hitbox.Y, action.hitbox.Z)
		end),
	})

	self.actionHitboxH = tab:AddSlider(bid(kind, "ActionHitboxH"), {
		Text = "Action Hitbox Height",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:anc(function(action, value)
			action.hitbox = Vector3.new(action.hitbox.X, value, action.hitbox.Z)
		end),
	})

	self.actionHitboxL = tab:AddSlider(bid(kind, "ActionHitboxL"), {
		Text = "Action Hitbox Length",
		Min = 0,
		Max = 100,
		Default = 0,
		Rounding = 1,
		Callback = self:anc(function(action, value)
			action.hitbox = Vector3.new(action.hitbox.X, action.hitbox.Y, value)
		end),
	})

	self.actionIhbc = tab:AddToggle(bid(kind, "ActionIhbc"), {
		Text = "Ignore Hitbox Check",
		Default = false,
		Callback = self:anc(function(action, value)
			action.ihbc = value
		end),
	})

	self.actionKey = tab:AddInput(bid(kind, "ActionKey"), {
		Text = "Custom Key (KeyCode name / MB1 / MB2)",
		Callback = self:anc(function(action, value)
			action.key = value
		end),
	})

	self.actionRemote = tab:AddDropdown(bid(kind, "ActionRemote"), {
		Text = "Remote Template",
		Values = remoteTemplateNames(),
		AllowNull = true,
		Callback = self:anc(function(action, value)
			action.remote = value
		end),
	})

	self.actionName = tab:AddInput(bid(kind, "ActionName"), {
		Text = "Action Name",
	})

	tab:AddButton({
		Text = "Create Action",
		Func = function()
			if not self.timingList.Value then
				return Logger.warn("No timing selected.")
			end

			local timing = self.container:find(self.timingList.Value)

			if not timing then
				return
			end

			if not self:acheck(timing) then
				return
			end

			local action = Action.new()
			action.name = self.actionName.Value
			action._type = self.actionType.Value or "Parry"
			action._when = tonumber(self.actionDelay.Value) or 0
			action.hitbox =
				Vector3.new(self.actionHitboxW.Value or 0, self.actionHitboxH.Value or 0, self.actionHitboxL.Value or 0)
			action.ihbc = self.actionIhbc.Value or false

			if action._type == "Custom Key" and self.actionKey.Value and #self.actionKey.Value > 0 then
				action.key = self.actionKey.Value
			end

			if action._type == "Remote" and self.actionRemote.Value then
				action.remote = self.actionRemote.Value
			end

			local ok, err = timing.actions:push(action)

			if not ok then
				return Logger.longNotify(err)
			end

			TimingStore.markDirty()
			self:arefresh(timing)
		end,
	})

	tab:AddButton({
		Text = "Duplicate Action",
		Func = function()
			if not self.timingList.Value or not self.actionList.Value then
				return Logger.warn("Select a timing and an action first.")
			end

			local timing = self.container:find(self.timingList.Value)
			local action = timing and timing.actions:find(self.actionList.Value)

			if not action then
				return
			end

			local clone = action:clone()
			local name = action.name .. " copy"
			local counter = 1

			while timing.actions:find(name) do
				counter = counter + 1
				name = action.name .. " copy " .. counter
			end

			clone.name = name
			timing.actions:push(clone)
			TimingStore.markDirty()
			self:arefresh(timing)
		end,
	})

	tab:AddButton({
		Text = "Remove Action",
		Func = function()
			if not self.timingList.Value or not self.actionList.Value then
				return Logger.warn("Select a timing and an action first.")
			end

			local timing = self.container:find(self.timingList.Value)
			local action = timing and timing.actions:find(self.actionList.Value)

			if not action then
				return
			end

			timing.actions:remove(action)
			TimingStore.markDirty()
			self:arefresh(timing)
		end,
	})
end

---@param kind string
---@param tab table
---@return BuilderSection
function BuilderSection.new(kind, tab)
	local self = setmetatable({}, BuilderSection)

	self.kind = kind
	self.container = config:get()[kind]
	self.module = TIMING_CLASSES[kind]
	self.loading = false

	self:build(tab)

	BuilderSections[kind] = self
	return self
end

--------------------------------------------------------------------------------
-- UI construction
--------------------------------------------------------------------------------

local RemoteUI = {
	parryLabel = nil,
	dodgeLabel = nil,
}

---Update the remote status labels.
local function updateRemoteLabels()
	if RemoteUI.parryLabel then
		local template = GameDataRemotes()["Parry"]
		local text = "Parry remote: " .. (template and template.path or "none")

		if template and GameDataRemotesDisabled()["Parry"] then
			text = text .. " (disabled)"
		end

		RemoteUI.parryLabel:SetText(text)
	end

	if RemoteUI.dodgeLabel then
		local template = GameDataRemotes()["Dodge"]
		local text = "Dodge remote: " .. (template and template.path or "none")

		if template and GameDataRemotesDisabled()["Dodge"] then
			text = text .. " (disabled)"
		end

		RemoteUI.dodgeLabel:SetText(text)
	end
end

---Parse the manual-args Lua table literal.
---@return table
local function parseManualArgs()
	local text = (Options.RC_ManualArgs and Options.RC_ManualArgs.Value) or ""

	if #text == 0 then
		return {}
	end

	local ok, result = pcall(function()
		return loadstringFn("return " .. text)()
	end)

	if ok and typeof(result) == "table" then
		return result
	end

	Logger.warn("Failed to parse manual args table: %s", tostring(result))
	return {}
end

---@param kind string
local function assignManual(kind)
	local path = Options.RC_ManualPath and Options.RC_ManualPath.Value

	if not path or #path == 0 then
		return Logger.warn("Enter a remote path first.")
	end

	saveRemoteTemplate(kind, {
		path = path,
		method = (Options.RC_ManualMethod and Options.RC_ManualMethod.Value) or "FireServer",
		args = parseManualArgs(),
	})

	updateRemoteLabels()
	Logger.notify("Set %s remote to '%s'.", kind, path)
end

---Build the Combat tab.
---@param tab table
local function buildCombatTab(tab)
	local defenseBox = tab:AddLeftGroupbox("Auto Defense")

	defenseBox
		:AddToggle("EnableAutoDefense", {
			Text = "Enable Auto Defense",
			Default = false,
		})
		:AddKeyPicker("EnableAutoDefenseKey", {
			Default = "None",
			SyncToggleState = true,
			Mode = "Toggle",
			Text = "Auto Defense",
		})

	defenseBox:AddDropdown("DefenseMode", {
		Text = "Defense Mode",
		Values = { "Key Emulation", "Remote" },
		Default = "Key Emulation",
	})

	defenseBox:AddLabel("Parry Key"):AddKeyPicker("ParryKey", {
		Default = "F",
		Mode = "Toggle",
		NoUI = true,
		Text = "Parry Key",
	})

	defenseBox:AddLabel("Dodge Key"):AddKeyPicker("DodgeKey", {
		Default = "Q",
		Mode = "Toggle",
		NoUI = true,
		Text = "Dodge Key",
	})

	defenseBox:AddSlider("KeyHoldTime", {
		Text = "Key Hold Time (ms)",
		Min = 0,
		Max = 500,
		Default = 50,
		Rounding = 0,
	})

	defenseBox:AddToggle("CompensatePing", {
		Text = "Compensate Ping",
		Default = true,
	})

	defenseBox:AddToggle("UseDodgeFallback", {
		Text = "Dodge When Parry On Cooldown",
		Default = false,
	})

	defenseBox:AddSlider("ParryCooldown", {
		Text = "Parry Cooldown (s)",
		Min = 0,
		Max = 5,
		Default = 0.25,
		Rounding = 2,
	})

	defenseBox:AddToggle("NotifyDefense", {
		Text = "Defense Notifications",
		Default = false,
	})

	local detectionBox = tab:AddRightGroupbox("Detection")

	detectionBox:AddSlider("MaxDetectionDistance", {
		Text = "Max Detection Distance",
		Min = 10,
		Max = 2000,
		Default = 300,
		Rounding = 0,
	})

	detectionBox:AddToggle("OnlyTargetPlayers", {
		Text = "Only Target Players",
		Default = false,
		Callback = function(value)
			if not value then
				-- Re-hook NPCs without needing a script re-run.
				Entities.rescan()
			end
		end,
	})

	detectionBox:AddToggle("VisualizeHitboxes", {
		Text = "Visualize Hitboxes",
		Default = false,
	})

	detectionBox:AddSlider("VisualizeLifetime", {
		Text = "Visualize Lifetime (s)",
		Min = 0.1,
		Max = 5,
		Default = 0.5,
		Rounding = 1,
	})

	detectionBox:AddSlider("DuihTimeout", {
		Text = "Delay-Until-In-Hitbox Timeout (s)",
		Min = 0.1,
		Max = 10,
		Default = 1.5,
		Rounding = 1,
	})

	local remoteBox = tab:AddRightGroupbox("Remote Defense")

	RemoteUI.parryLabel = remoteBox:AddLabel("Parry remote: none")
	RemoteUI.dodgeLabel = remoteBox:AddLabel("Dodge remote: none")

	remoteBox
		:AddButton({
			Text = "Stop Using Parry Remote",
			Func = function()
				GameDataRemotesDisabled()["Parry"] = true
				GameData.save()
				updateRemoteLabels()
			end,
		})
		:AddButton({
			Text = "Use Parry Remote",
			Func = function()
				GameDataRemotesDisabled()["Parry"] = nil
				GameData.save()
				updateRemoteLabels()
			end,
		})

	remoteBox
		:AddButton({
			Text = "Stop Using Dodge Remote",
			Func = function()
				GameDataRemotesDisabled()["Dodge"] = true
				GameData.save()
				updateRemoteLabels()
			end,
		})
		:AddButton({
			Text = "Use Dodge Remote",
			Func = function()
				GameDataRemotesDisabled()["Dodge"] = nil
				GameData.save()
				updateRemoteLabels()
			end,
		})

	remoteBox:AddButton({
		Text = "Use ABS Remotes",
		Func = function()
			saveRemoteTemplate("Parry", RemotePresets.ABS.Parry)
			saveRemoteTemplate("Dodge", RemotePresets.ABS.Dodge)

			pcall(function()
				Options.DefenseMode:SetValue("Remote")
			end)

			updateRemoteLabels()
			Logger.notify("ABS parry/dodge remotes applied and remote mode enabled.")
		end,
	})

	remoteBox:AddButton({
		Text = "Delete Saved Remotes",
		Func = function()
			GameDataRemotes()["Parry"] = nil
			GameDataRemotes()["Dodge"] = nil
			GameDataRemotesDisabled()["Parry"] = nil
			GameDataRemotesDisabled()["Dodge"] = nil
			GameData.save()
			updateRemoteLabels()
			Logger.notify("Saved remotes deleted.")
		end,
	})

	remoteBox:AddDivider()

	remoteBox:AddInput("RC_ManualPath", {
		Text = 'Manual Remote Path (game:GetService("X").A.B OK)',
	})

	remoteBox:AddDropdown("RC_ManualMethod", {
		Text = "Manual Method",
		Values = { "FireServer", "InvokeServer" },
		Default = "FireServer",
	})

	remoteBox:AddInput("RC_ManualArgs", {
		Text = "Manual Args (Lua table; $AIM_POS, $ENUM:X.Y, $LOCALPLAYER ok)",
	})

	remoteBox:AddButton({
		Text = "Set Manual As Parry",
		Func = function()
			assignManual("Parry")
		end,
	})

	remoteBox:AddButton({
		Text = "Set Manual As Dodge",
		Func = function()
			assignManual("Dodge")
		end,
	})

	remoteBox:AddButton({
		Text = "Test Parry Remote",
		Func = function()
			local template = GameDataRemotes()["Parry"]

			if not template then
				return Logger.warn("No parry remote set.")
			end

			RemoteResolver.fire(template)
		end,
	})

	remoteBox:AddButton({
		Text = "Test Dodge Remote",
		Func = function()
			local template = GameDataRemotes()["Dodge"]

			if not template then
				return Logger.warn("No dodge remote set.")
			end

			RemoteResolver.fire(template)
		end,
	})
end

---Build the Builder tab.
---@param tab table
---@return table labels for periodic updates
local function buildBuilderTab(tab)
	local tabbox = tab:AddTabbox({ Name = "Builder", Side = 1 })

	local sections = {}
	local tabNames = {
		{ kind = "animation", name = "Animation" },
		{ kind = "sound", name = "Sound" },
		{ kind = "part", name = "Part" },
		{ kind = "effect", name = "Effect" },
	}

	for _, info in next, tabNames do
		local sectionTab = tabbox:AddTab(info.name)
		sections[info.kind] = BuilderSection.new(info.kind, sectionTab)
	end

	local filesBox = tab:AddRightGroupbox("Timings Files")

	filesBox:AddToggle("PeriodicAutoSave", {
		Text = "Periodic Auto Save",
		Default = false,
	})

	filesBox:AddSlider("PeriodicAutoSaveInterval", {
		Text = "Auto Save Interval (s)",
		Min = 5,
		Max = 300,
		Default = 15,
		Rounding = 0,
	})

	filesBox:AddInput("TimingsName", {
		Text = "Timings File Name",
	})

	local timingsList = filesBox:AddDropdown("TimingsList", {
		Text = "Timings Files",
		Values = TimingStore.list(),
		AllowNull = true,
	})

	local loadedLabel = filesBox:AddLabel("Loaded: none")

	local function refreshFiles()
		timingsList:SetValues(TimingStore.list())
	end

	local function selectedFile()
		return Options.TimingsList and Options.TimingsList.Value or nil
	end

	filesBox:AddButton({
		Text = "Create",
		Func = function()
			local name = Options.TimingsName and Options.TimingsName.Value

			if not name or #name == 0 then
				return Logger.warn("Enter a timings file name first.")
			end

			TimingStore.create(name)
			refreshFiles()
			refreshAllSections()
		end,
	})

	filesBox:AddButton({
		Text = "Load (Double Click)",
		DoubleClick = true,
		Func = function()
			local name = selectedFile()

			if not name then
				return Logger.warn("Select a timings file first.")
			end

			TimingStore.load(name)
			refreshAllSections()
		end,
	})

	filesBox:AddButton({
		Text = "Save",
		Func = function()
			local name = Options.TimingsName and Options.TimingsName.Value
			name = (#(name or "") > 0) and name or TimingStore.current

			if not name then
				return Logger.warn("Enter a timings file name or load a file first.")
			end

			TimingStore.save(name)
			refreshFiles()
		end,
	})

	filesBox:AddButton({
		Text = "Clear (Double Click)",
		DoubleClick = true,
		Func = function()
			local name = selectedFile() or TimingStore.current

			if not name then
				return Logger.warn("Select a timings file first.")
			end

			TimingStore.clear(name)
			refreshAllSections()
		end,
	})

	filesBox:AddButton({
		Text = "Delete (Double Click)",
		DoubleClick = true,
		Func = function()
			local name = selectedFile()

			if not name then
				return Logger.warn("Select a timings file first.")
			end

			TimingStore.delete(name)
			refreshFiles()
		end,
	})

	filesBox:AddButton({
		Text = "Refresh",
		Func = refreshFiles,
	})

	filesBox:AddButton({
		Text = "Set As Auto Load (this game)",
		Func = function()
			local name = selectedFile() or TimingStore.current

			if not name then
				return Logger.warn("Select a timings file first.")
			end

			TimingStore.autoload(name)
			Logger.notify("'%s' will auto-load in this game.", name)
		end,
	})

	local logBox = tab:AddRightGroupbox("Logger")

	local visualizerToggle = logBox:AddToggle("ShowAnimationVisualizer", {
		Text = "Show Animation Visualizer",
		Default = false,
		Callback = function(value)
			AnimationVisualizer.visible(value)
		end,
	})

	visualizerToggle:AddKeyPicker("AnimationVisualizerKeyBind", {
		Default = "N/A",
		SyncToggleState = true,
		Text = "Animation Visualizer",
	})

	local showLoggerToggle = logBox:AddToggle("ShowLoggerWindow", {
		Text = "Show Logger Window",
		Default = false,
		Callback = function(value)
			InfoLogger.visible(value)
		end,
	})

	showLoggerToggle:AddKeyPicker("ShowLoggerWindowKeyBind", {
		Default = "N/A",
		SyncToggleState = true,
		Text = "Logger Window",
	})

	logBox:AddSlider("MinimumLoggerDistance", {
		Text = "Minimum Logger Distance",
		Min = 0,
		Max = 100,
		Rounding = 0,
		Suffix = "m",
		Default = 0,
	})

	logBox:AddSlider("MaximumLoggerDistance", {
		Text = "Maximum Logger Distance",
		Min = 0,
		Max = 1000,
		Rounding = 0,
		Suffix = "m",
		Default = 1000,
	})

	local blacklistedKeys = logBox:AddDropdown("BlacklistedKeys", {
		Text = "Blacklisted Keys",
		Values = InfoLogger.keyBlacklists(),
		Multi = true,
		AllowNull = true,
	})

	logBox:AddButton({
		Text = "Remove Selected Keys",
		Func = function()
			for selected in next, blacklistedKeys.Value do
				InfoLogger.Data.KeyBlacklistList[selected] = nil
			end

			GameData.data.blacklist = InfoLogger.Data.KeyBlacklistList
			GameData.save()

			blacklistedKeys:SetValues(InfoLogger.keyBlacklists())
			blacklistedKeys:SetValue({})
		end,
	})

	local simBox = tab:AddRightGroupbox("Hitbox Simulation")

	simBox:AddToggle("ShowHitboxSimulation", {
		Text = "Show Hitbox Simulation",
		Default = false,
	})

	simBox:AddDropdown("HS_HitboxType", {
		Text = "Hitbox Type",
		Values = { "Block", "Ball", "Cylinder" },
		Default = "Block",
	})

	simBox:AddSlider("HS_HitboxSizeX", {
		Text = "Hitbox Size X",
		Min = 0.1,
		Max = 100,
		Default = 4,
		Rounding = 1,
	})

	simBox:AddSlider("HS_HitboxSizeY", {
		Text = "Hitbox Size Y",
		Min = 0.1,
		Max = 100,
		Default = 4,
		Rounding = 1,
	})

	simBox:AddSlider("HS_HitboxSizeZ", {
		Text = "Hitbox Size Z",
		Min = 0.1,
		Max = 100,
		Default = 4,
		Rounding = 1,
	})

	simBox:AddToggle("HS_FacingOffset", {
		Text = "Hitbox Facing Offset",
		Default = false,
	})

	simBox:AddSlider("HS_ShiftOffset", {
		Text = "Hitbox Shift Offset",
		Min = -10,
		Max = 10,
		Default = 0,
		Rounding = 1,
	})

	return {
		sections = sections,
		loadedLabel = loadedLabel,
	}
end

---Refresh all builder section timing lists (e.g. after a file load/clear).
refreshAllSections = function()
	for _, section in next, BuilderSections do
		section:refresh()
		section:reset()
	end
end

---Build the Tools tab.
---@param tab table
local function buildToolsTab(tab)
	local diffBox = tab:AddLeftGroupbox("Difference Calculator")

	diffBox:AddToggle("DiffEnabled", {
		Text = "Enable Difference Calculator",
		Default = false,
	})

	diffBox:AddInput("DiffAnimationId", {
		Text = "Animation ID",
	})

	diffBox:AddSlider("DiffMaxWindow", {
		Text = "Max Damage Window (s)",
		Min = 0.5,
		Max = 15,
		Default = 5,
		Rounding = 1,
	})

	diffBox:AddToggle("DiffSubtractPing", {
		Text = "Subtract Half Ping On Copy",
		Default = true,
	})

	diffBox:AddButton({
		Text = "Use Last Clicked Key",
		Func = function()
			local id = InfoLogger.lastClickedKey

			if not id then
				return Logger.warn("Click an entry in the Info Logger first.")
			end

			if Options.DiffAnimationId then
				Options.DiffAnimationId:SetValue(id)
			end
		end,
	})

	DifferenceCalculator.ui.lastLabel = diffBox:AddLabel("Last: -")
	DifferenceCalculator.ui.statsLabel = diffBox:AddLabel("Average: - | Min: - | Max: - | Count: 0")

	DifferenceCalculator.ui.samplesList = diffBox:AddDropdown("DiffSamplesList", {
		Text = "Samples",
		Values = {},
		AllowNull = true,
	})

	diffBox:AddButton({
		Text = "Clear Samples",
		Func = function()
			DifferenceCalculator.clear()
		end,
	})

	diffBox:AddButton({
		Text = "Copy Last To Action Delay",
		Func = function()
			local count = #DifferenceCalculator.samples

			if count == 0 then
				return Logger.warn("No samples recorded yet.")
			end

			local last = DifferenceCalculator.samples[count]
			local subtract = (Toggles.DiffSubtractPing and Toggles.DiffSubtractPing.Value) and (last.ping / 2) or 0
			local delay = math.floor(last.ms - subtract + 0.5)

			-- Apply to whichever builder section currently has an action selected.
			for _, section in next, BuilderSections do
				if section.actionList.Value and section.timingList.Value then
					local timing = section.container:find(section.timingList.Value)
					local action = timing and timing.actions:find(section.actionList.Value)

					if action then
						section.loading = true
						section.actionDelay:SetValue(delay)
						section.loading = false
						action._when = delay
						TimingStore.markDirty()
						Logger.notify("Set action '%s' delay to %d ms.", action.name, delay)
						return
					end
				end
			end

			Logger.warn("Select an action in the Builder tab to copy the delay to.")
		end,
	})

	diffBox:AddButton({
		Text = "Export Samples",
		Func = function()
			DifferenceCalculator.export()
		end,
	})

	local learnBox = tab:AddLeftGroupbox("Auto Learn Timings")

	learnBox:AddToggle("AutoLearnEnabled", {
		Text = "Enable Auto Learn",
		Default = false,
	})

	learnBox:AddInput("AutoLearnIds", {
		Text = "Animation IDs (comma/space separated)",
		Default = table.concat(AutoLearn.ids(), ", "),
		Callback = function(value)
			local list = {}

			for token in tostring(value):gmatch("[^,%s]+") do
				local id = normalizeAssetId(token)

				if #id > 0 then
					table.insert(list, id)
				end
			end

			AutoLearn.setIds(list)
		end,
	})

	learnBox:AddButton({
		Text = "Add Last Clicked Logger Key",
		Func = function()
			local key = InfoLogger.lastClickedKey

			if not key then
				return Logger.warn("Click an entry in the Info Logger first.")
			end

			local ids = AutoLearn.ids()
			local id = normalizeAssetId(key)

			for _, existing in next, ids do
				if existing == id then
					return
				end
			end

			table.insert(ids, id)

			if Options.AutoLearnIds then
				Options.AutoLearnIds:SetValue(table.concat(ids, ", "))
			else
				AutoLearn.setIds(ids)
			end
		end,
	})

	learnBox:AddButton({
		Text = "Clear IDs",
		Func = function()
			if Options.AutoLearnIds then
				Options.AutoLearnIds:SetValue("")
			else
				AutoLearn.setIds({})
			end
		end,
	})

	AutoLearn.ui.listLabel = learnBox:AddLabel(string.format("Watching: %d IDs", #AutoLearn.ids()))

	learnBox:AddInput("AutoLearnHealthPath", {
		Text = "HP Path (blank = LocalPlayer Humanoid.Health; game:GetService(...) paths OK)",
		Default = AutoLearn.healthPath(),
		Callback = function(value)
			GameData.data.autoLearnHealthPath = tostring(value)
			GameData.save()
			AutoLearn.healthParent = nil
		end,
	})

	learnBox:AddToggle("AutoLearnAnyChange", {
		Text = "Count Any HP Change (not just damage)",
		Default = false,
	})

	learnBox:AddSlider("AutoLearnDamageWindow", {
		Text = "Damage Window (ms)",
		Min = 100,
		Max = 5000,
		Default = 2000,
		Rounding = 0,
	})

	learnBox:AddSlider("AutoLearnPadding", {
		Text = "Hitbox Padding (studs)",
		Min = 0,
		Max = 10,
		Default = 1,
		Rounding = 1,
	})

	learnBox:AddToggle("AutoLearnUpdateExisting", {
		Text = "Update Existing Timings",
		Default = true,
	})

	AutoLearn.ui.statusLabel = learnBox:AddLabel("Status: idle")

	learnBox:AddLabel(
		"Get hit by the watched animation; delay = animation start -> HP change, hitbox = NPC distance at the hit."
	)

	local infoBox = tab:AddRightGroupbox("Info")

	infoBox:AddLabel("PlaceId: " .. tostring(placeId))
	infoBox:AddLabel("Executor: " .. ((identifyexecutor and identifyexecutor()) or "Unknown"))
	infoBox:AddLabel("Storage root: " .. ROOT_FOLDER)
	infoBox:AddLabel("Filesystem available: " .. tostring(FS_AVAILABLE and true or false))
end

---Build the Settings tab.
---@param tab table
local function buildSettingsTab(tab)
	local menuBox = tab:AddLeftGroupbox("Menu")

	menuBox:AddLabel("Menu keybind"):AddKeyPicker("MenuKeybind", {
		Default = "RightShift",
		NoUI = true,
		Text = "Menu keybind",
	})

	menuBox:AddToggle("ShowKeybinds", {
		Text = "Show Keybinds",
		Default = false,
		Callback = function(value)
			Library.KeybindFrame.Visible = value
		end,
	})

	menuBox:AddToggle("Watermark", {
		Text = "Show Watermark",
		Default = false,
	})

	menuBox:AddButton({
		Text = "Unload",
		Func = function()
			local uapb = getgenvSafe().UAPB

			if uapb and uapb.unload then
				uapb.unload()
			end
		end,
	})

	if ThemeManager then
		ThemeManager:SetLibrary(Library)
		ThemeManager:SetFolder(ROOT_FOLDER .. "/" .. CONFIGS_FOLDER)
		ThemeManager:ApplyToTab(tab)
	end

	if SaveManager then
		SaveManager:SetLibrary(Library)
		SaveManager:IgnoreThemeSettings()
		SaveManager:SetIgnoreIndexes({ "MenuKeybind" })
		SaveManager:SetFolder(ROOT_FOLDER .. "/" .. CONFIGS_FOLDER)
		SaveManager:BuildConfigSection(tab)
	end
end

--------------------------------------------------------------------------------
-- init / unload
--------------------------------------------------------------------------------

local initialized = false
local unloading = false
local builderUI = nil
local heartbeatAccumulator = 0
local fpsCounter = 60

---Per-frame housekeeping.
---@param dt number
local function onHeartbeat(dt)
	if dt and dt > 0 then
		fpsCounter = math.floor(1 / dt + 0.5)
	end

	Simulation.step()

	heartbeatAccumulator = heartbeatAccumulator + (dt or 0)

	if heartbeatAccumulator < 0.5 then
		return
	end

	heartbeatAccumulator = 0

	if Toggles and Toggles.Watermark and Toggles.Watermark.Value then
		Library:SetWatermark(string.format("UAPB | %s | %d fps | %d ms", "running", fpsCounter, Latency.rtt() * 1000))
	else
		Library:SetWatermarkVisibility(false)
	end

	TimingStore.heartbeat()
	Entities.trackPlayback()

	if builderUI and builderUI.loadedLabel then
		local text = string.format(
			"Loaded: %s%s",
			TimingStore.current or "none",
			TimingStore.dirty and " (unsaved changes)" or ""
		)

		if builderUI.lastLabelText ~= text then
			builderUI.lastLabelText = text
			builderUI.loadedLabel:SetText(text)
		end
	end
end

---Unload everything.
local function unload()
	if unloading then
		return
	end

	unloading = true
	UNLOADED = true

	-- Persist anything dirty.
	if TimingStore.dirty and TimingStore.current then
		pcall(TimingStore.save, TimingStore.current)
	end

	pcall(GameData.save)

	pcall(InfoLogger.detach)
	pcall(AnimationVisualizer.detach)
	pcall(Simulation.clear)
	pcall(Hitbox.clean)
	pcall(function()
		Entities.maid:clean()
	end)
	pcall(function()
		DifferenceCalculator.maid:clean()
	end)
	pcall(AutoLearn.stop)
	pcall(function()
		for _, state in next, Entities.tracked do
			state.maid:clean()
		end
		table.clear(Entities.tracked)
	end)

	rootMaid:clean()

	if Library then
		pcall(function()
			Library:Unload()
		end)
	end

	getgenvSafe().UAPB = nil
end

---Initialize the script.
local function init()
	if initialized then
		return
	end

	if not loadstringFn then
		return error("[UAPB] loadstring is unavailable on this executor.")
	end

	if not loadLibraries() then
		return error("[UAPB] Failed to load the Linoria UI library.")
	end

	initialized = true

	GameData.load()

	Window = Library:CreateWindow({
		Title = "UAPB",
		Center = true,
		AutoShow = true,
		TabPadding = 8,
		MenuFadeTime = 0.2,
	})

	local combatTab = Window:AddTab("Combat")
	local builderTab = Window:AddTab("Builder")
	local toolsTab = Window:AddTab("Tools")
	local settingsTab = Window:AddTab("Settings")

	buildCombatTab(combatTab)
	builderUI = buildBuilderTab(builderTab)
	buildToolsTab(toolsTab)
	buildSettingsTab(settingsTab)

	InfoLogger.init()
	AnimationVisualizer.init()

	Library.ToggleKeybind = Options.MenuKeybind

	updateRemoteLabels()
	refreshRemoteDropdowns()

	DifferenceCalculator.start()
	AutoLearn.start()
	Entities.start()

	rootMaid:mark(runService.Heartbeat:Connect(onHeartbeat))
	rootMaid:mark(runService.RenderStepped:Connect(InfoLogger.renderStepped))
	rootMaid:mark(Simulation.maid)
	rootMaid:mark(Entities.maid)
	rootMaid:mark(DifferenceCalculator.maid)
	rootMaid:mark(AutoLearn.maid)

	Library:OnUnload(unload)

	-- Per-game timing autoload.
	local autoloadName = GameData.data.autoloadTimings

	if autoloadName and FS_AVAILABLE then
		local fs = timingsFs()

		if fs and fs:file(autoloadName .. ".json") then
			TimingStore.load(autoloadName)
			refreshAllSections()
		end
	end

	if SaveManager then
		pcall(function()
			SaveManager:LoadAutoloadConfig()
		end)
	end

	getgenvSafe().UAPB = {
		unload = unload,
		TimingStore = TimingStore,
		Defense = Defense,
		Input = Input,
		RemoteResolver = RemoteResolver,
		config = config,
	}

	Logger.notify("UAPB loaded — timings stored in workspace/UAPB/Timings.")
end

init()
