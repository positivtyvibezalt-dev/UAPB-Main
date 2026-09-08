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
		UAPB/Games/<PlaceId>.json           per-game data (captured remotes, autoload timing name)
		UAPB/Logs/animations_<PlaceId>.json logged animation ids
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

local newcclosure = env("newcclosure")
local hookmetamethod = env("hookmetamethod")
local getnamecallmethod = env("getnamecallmethod")
local checkcaller = env("checkcaller")
local getgc = env("getgc")
local getrawmetatable = env("getrawmetatable")
local identifyexecutor = env("identifyexecutor")

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
-- RemoteResolver + RemoteCapture
--------------------------------------------------------------------------------

---@class RemoteTemplate
---@field path string
---@field method string "FireServer"|"InvokeServer"
---@field args table
---@field name string

local GameDataRemotes -- alias kept for readability: GameData.data.remotes

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

---Walk a dotted path from game, supporting names containing '.' via a last-segment descendant match.
---@param path string
---@return Instance?
local function walkPath(path)
	local current = game

	for segment in string.gmatch(path, "[^%.]+") do
		current = current and current:FindFirstChild(segment)

		if not current then
			break
		end
	end

	if current then
		return current
	end

	-- Last-segment descendant match for names containing dots or non-direct paths.
	local last = path:match("([^%.]+)$")

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

	local name = pathOrName:match("([^%.]+)$") or pathOrName

	if RemoteResolver.cache[pathOrName] then
		local cached = RemoteResolver.cache[pathOrName]

		if cached and cached.Parent then
			return cached
		end

		RemoteResolver.cache[pathOrName] = nil
	end

	-- 1. Walk the dotted path.
	if pathOrName:find("%.") then
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

---Substitute special markers in captured/user-typed args.
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
	local ok, err = pcall(remote[method], remote, unpackFn(args))

	if not ok then
		RemoteResolver.cache[template.path or template.name] = nil
		Logger.warn("Remote '%s' failed: %s", template.path or template.name, err)
	end

	return ok, err
end

---@class RemoteCapture
local RemoteCapture = {
	capturing = nil,
	captureDeadline = 0,
	buffer = {},
	installed = false,
	hookOriginal = nil,
}

---Convert a value into a JSON-serializable form.
---@param value any
---@return any
local function serializeArg(value)
	local valueType = typeof(value)

	if valueType == "Instance" then
		return "$INSTANCE:" .. value:GetFullName()
	elseif valueType == "CFrame" then
		return { __type = "CFrame", components = { value:GetComponents() } }
	elseif valueType == "Vector3" then
		return { __type = "Vector3", components = { value.X, value.Y, value.Z } }
	elseif valueType == "Vector2" then
		return { __type = "Vector2", components = { value.X, value.Y } }
	elseif valueType == "number" or valueType == "string" or valueType == "boolean" or valueType == "nil" then
		return value
	elseif valueType == "table" then
		local out = {}
		local convertible = true

		for key, item in next, value do
			if typeof(key) ~= "string" and typeof(key) ~= "number" then
				convertible = false
				break
			end

			local serialized = serializeArg(item)

			if serialized == nil then
				convertible = false
				break
			end

			out[key] = serialized
		end

		if convertible then
			return out
		end

		return tostring(value)
	end

	return tostring(value)
end

---@param list table
---@return table
local function serializeArgs(...)
	local out = {}

	for idx = 1, select("#", ...) do
		out[idx] = serializeArg(select(idx, ...))
	end

	return out
end

---Check whether a remote name is ignored by the capture filter.
---@param name string
---@return boolean
local function captureIgnored(name)
	local filter = (Options and Options.CaptureIgnore and Options.CaptureIgnore.Value)
		or "Ping,Heartbeat,Replicate,Position,Camera"

	for word in string.gmatch(filter, "[^,]+") do
		word = word:gsub("^%s+", ""):gsub("%s+$", "")

		if #word > 0 and name:lower():find(word:lower(), 1, true) then
			return true
		end
	end

	return false
end

---Install the universal __namecall hook (lazy, first capture only).
function RemoteCapture.install()
	if RemoteCapture.installed then
		return
	end

	if not (hookmetamethod and getnamecallmethod and checkcaller) then
		return
	end

	RemoteCapture.installed = true

	local hookFn
	hookFn = function(self, ...)
		local method = getnamecallmethod()

		if
			not UNLOADED
			and not checkcaller()
			and (method == "FireServer" or method == "InvokeServer")
			and RemoteCapture.capturing
			and os.clock() <= RemoteCapture.captureDeadline
			and typeof(self) == "Instance"
			and isRemote(self)
			and not captureIgnored(self.Name)
		then
			if #RemoteCapture.buffer < 20 then
				table.insert(RemoteCapture.buffer, {
					path = self:GetFullName(),
					method = method,
					args = serializeArgs(...),
				})
			end
		end

		return RemoteCapture.hookOriginal(self, ...)
	end

	RemoteCapture.hookOriginal = hookmetamethod(game, "__namecall", newcclosure and newcclosure(hookFn) or hookFn)
end

---Begin capturing remotes of a kind ("Parry" or "Dodge").
---@param kind string
function RemoteCapture.start(kind)
	if not (hookmetamethod and getnamecallmethod and checkcaller) then
		return Logger.notify("Executor lacks hookmetamethod; remote capture unavailable.")
	end

	RemoteCapture.install()

	RemoteCapture.capturing = kind
	RemoteCapture.buffer = {}
	RemoteCapture.captureDeadline = os.clock()
		+ ((Options and Options.CaptureWindow and Options.CaptureWindow.Value) or 5)

	Logger.notify("Capturing remotes for '%s' — perform the action now.", kind)
end

---Stop capturing.
function RemoteCapture.stop()
	RemoteCapture.capturing = nil
end

---Persist a remote template into per-game data.
---@param name string
---@param template RemoteTemplate
function RemoteCapture.saveTemplate(name, template)
	GameDataRemotes()[name] = {
		path = template.path,
		method = template.method,
		args = template.args,
		name = name,
	}

	GameData.save()
end

---@return table
function GameDataRemotes()
	GameData.data.remotes = GameData.data.remotes or {}
	return GameData.data.remotes
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
-- Forward declarations
--------------------------------------------------------------------------------

local Defense
local AnimationLog
local DifferenceCalculator
local Entities

--------------------------------------------------------------------------------
-- Entities (universal entity discovery)
--------------------------------------------------------------------------------

---@class Entities
Entities = {
	tracked = {}, -- model -> state { maid, humanoid, root, lastTrack, lastAt }
	maid = Maid.new(),
}

---Is a model a valid entity (Humanoid + HumanoidRootPart)?
---@param model any
---@return boolean
local function isEntity(model)
	if typeof(model) ~= "Instance" or not model:IsA("Model") then
		return false
	end

	if not model:FindFirstChildOfClass("Humanoid") then
		return false
	end

	if not model:FindFirstChild("HumanoidRootPart") then
		return false
	end

	return true
end

---Distance between the local root and an entity.
---@param entity Model
---@return number?
local function entityDistance(entity)
	local localRoot = Input.localRoot()
	local root = entity and entity:FindFirstChild("HumanoidRootPart")

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

	local maxDistance = (Options and Options.MaxDetectionDistance and Options.MaxDetectionDistance.Value) or 300
	local distance = entityDistance(entity)

	if distance and distance > maxDistance then
		return
	end

	if AnimationLog then
		AnimationLog.log(entity, track)
	end

	if DifferenceCalculator then
		DifferenceCalculator.onAnimation(entity, track)
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

	local state = {
		maid = maid,
		humanoid = humanoid,
		lastTrack = nil,
		lastAt = 0,
	}

	Entities.tracked[entity] = state

	-- Animation signals.
	if humanoid then
		maid:mark(humanoid.AnimationPlayed:Connect(function(track)
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

	if humanoid then
		local animator = humanoid:FindFirstChildOfClass("Animator")

		if animator then
			hookAnimator(animator)
		else
			maid:mark(humanoid.ChildAdded:Connect(function(child)
				if child:IsA("Animator") then
					hookAnimator(child)
				end
			end))
		end
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

	-- Cleanup when the entity is removed.
	maid:mark(entity.AncestryChanged:Connect(function()
		if not entity:IsDescendantOf(workspace) then
			local tracked = Entities.tracked[entity]

			if tracked then
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
		local root = model:FindFirstChild("HumanoidRootPart")

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

--------------------------------------------------------------------------------
-- AnimationLog
--------------------------------------------------------------------------------

---@class AnimationLog
AnimationLog = {
	entries = {}, -- ring buffer, most recent last
	seen = {}, -- id -> {name, entity, count, last}
	dirty = false,
	lastFlush = 0,
	fs = nil,
}

---@return Filesystem?
local function logsFs()
	if not FS_AVAILABLE then
		return nil
	end

	AnimationLog.fs = AnimationLog.fs or Filesystem.new(LOGS_FOLDER)
	return AnimationLog.fs
end

---Load the persisted seen map.
function AnimationLog.load()
	local fs = logsFs()

	if not fs then
		return
	end

	pcall(function()
		local file = "animations_" .. tostring(placeId) .. ".json"

		if fs:file(file) then
			AnimationLog.seen = httpService:JSONDecode(fs:read(file)) or {}
		end
	end)
end

---Flush the seen map to disk if dirty (call every Heartbeat; writes are debounced).
function AnimationLog.flush()
	if not AnimationLog.dirty then
		return
	end

	if os.clock() - AnimationLog.lastFlush < 5 then
		return
	end

	local fs = logsFs()

	if not fs then
		return
	end

	AnimationLog.lastFlush = os.clock()
	AnimationLog.dirty = false

	pcall(function()
		fs:write("animations_" .. tostring(placeId) .. ".json", httpService:JSONEncode(AnimationLog.seen))
	end)
end

---Record a played animation.
---@param entity Model
---@param track AnimationTrack
function AnimationLog.log(entity, track)
	if not track or not track.Animation then
		return
	end

	if not (Toggles and Toggles.AnimationLogger and Toggles.AnimationLogger.Value) then
		return
	end

	if
		Toggles
		and Toggles.IgnoreCoreAnimations
		and Toggles.IgnoreCoreAnimations.Value
		and track.Priority == Enum.AnimationPriority.Core
	then
		return
	end

	local id = normalizeAssetId(track.Animation.AnimationId)

	table.insert(AnimationLog.entries, {
		id = id,
		name = track.Animation.Name,
		entity = entity and entity.Name or "?",
		at = os.clock(),
		speed = track.Speed,
		priority = tostring(track.Priority),
	})

	if #AnimationLog.entries > 200 then
		table.remove(AnimationLog.entries, 1)
	end

	local seen = AnimationLog.seen[id]

	if seen then
		seen.count = (seen.count or 0) + 1
		seen.last = os.time()
		seen.name = track.Animation.Name
		seen.entity = entity and entity.Name or "?"
	else
		AnimationLog.seen[id] = {
			name = track.Animation.Name,
			entity = entity and entity.Name or "?",
			count = 1,
			last = os.time(),
		}
	end

	AnimationLog.dirty = true
end

---Refresh the UI dropdown values, most recent first.
---@param dropdown table
function AnimationLog.refreshDropdown(dropdown)
	local values = {}

	for idx = #AnimationLog.entries, 1, -1 do
		local entry = AnimationLog.entries[idx]
		table.insert(values, string.format("%s | %s | %s", entry.id, entry.name, entry.entity))
	end

	dropdown:SetValues(values)
end

---Clear the log.
function AnimationLog.clear()
	table.clear(AnimationLog.entries)
	table.clear(AnimationLog.seen)
	AnimationLog.dirty = true
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
	local fs = logsFs()

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

	local timing = config:get().animation:index(normalizeAssetId(track.Animation.AnimationId))

	if not timing then
		return
	end

	local root = entity and entity:FindFirstChild("HumanoidRootPart")

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing, track)
end

---Handle a descendant added to an entity (effect timings).
---@param entity Model
---@param inst Instance
function Defense.onEffect(entity, inst)
	local timing = config:get().effect:index(inst.Name)

	if not timing then
		return
	end

	local root = entity and entity:FindFirstChild("HumanoidRootPart")

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing)
end

---Handle a sound that started playing on an entity.
---@param entity Model
---@param sound Sound
function Defense.onSound(entity, sound)
	local timing = config:get().sound:index(normalizeAssetId(sound.SoundId))

	if not timing then
		return
	end

	local root = entity and entity:FindFirstChild("HumanoidRootPart")

	if not root then
		return
	end

	Defense.dispatch(entity, root, timing)
end

---Handle a BasePart added to workspace (part timings).
---@param part BasePart
function Defense.onPart(part)
	local timing = config:get().part:index(part.Name)

	if not timing then
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
	captured = nil,
}

---Update the remote status labels.
local function updateRemoteLabels()
	if RemoteUI.parryLabel then
		local template = GameDataRemotes()["Parry"]
		RemoteUI.parryLabel:SetText("Parry remote: " .. (template and template.path or "none"))
	end

	if RemoteUI.dodgeLabel then
		local template = GameDataRemotes()["Dodge"]
		RemoteUI.dodgeLabel:SetText("Dodge remote: " .. (template and template.path or "none"))
	end
end

---@param entry table
---@return string
local function captureEntryLabel(idx, entry)
	local preview = ""

	local ok, encoded = pcall(httpService.JSONEncode, httpService, entry.args)

	if ok and type(encoded) == "string" then
		preview = encoded

		if #preview > 60 then
			preview = preview:sub(1, 60) .. "..."
		end
	end

	return string.format("%d. %s (%s) %s", idx, entry.path, entry.method, preview)
end

---Refresh the captured-remotes dropdown.
local function refreshCaptured()
	if not RemoteUI.captured then
		return
	end

	local values = {}

	for idx, entry in next, RemoteCapture.buffer do
		table.insert(values, captureEntryLabel(idx, entry))
	end

	RemoteUI.captured:SetValues(values)
end

---Parse the selected capture entry index.
---@return table?
local function selectedCapture()
	local value = RemoteUI.captured and RemoteUI.captured.Value

	if not value then
		return nil
	end

	local idx = tonumber(tostring(value):match("^(%d+)%."))

	if not idx then
		return nil
	end

	return RemoteCapture.buffer[tonumber(idx)]
end

---@param kind string
local function assignCaptured(kind)
	local entry = selectedCapture()

	if not entry then
		return Logger.warn("No captured remote selected.")
	end

	RemoteCapture.saveTemplate(kind, entry)
	updateRemoteLabels()
	Logger.notify("Set %s remote to '%s'.", kind, entry.path)
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

	RemoteCapture.saveTemplate(kind, {
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
	})

	detectionBox:AddToggle("IgnoreCoreAnimations", {
		Text = "Ignore Core Animations",
		Default = true,
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

	remoteBox:AddSlider("CaptureWindow", {
		Text = "Capture Window (s)",
		Min = 1,
		Max = 30,
		Default = 5,
		Rounding = 0,
	})

	remoteBox:AddInput("CaptureIgnore", {
		Text = "Capture Ignore Filter",
		Default = "Ping,Heartbeat,Replicate,Position,Camera",
	})

	remoteBox:AddButton({
		Text = "Capture (Parry)",
		Func = function()
			RemoteCapture.start("Parry")
		end,
	})

	remoteBox:AddButton({
		Text = "Capture (Dodge)",
		Func = function()
			RemoteCapture.start("Dodge")
		end,
	})

	RemoteUI.captured = remoteBox:AddDropdown("RC_Captured", {
		Text = "Captured Remotes",
		Values = {},
		AllowNull = true,
	})

	remoteBox:AddButton({
		Text = "Refresh Captured List",
		Func = refreshCaptured,
	})

	remoteBox:AddButton({
		Text = "Use Selected For Parry",
		Func = function()
			assignCaptured("Parry")
		end,
	})

	remoteBox:AddButton({
		Text = "Use Selected For Dodge",
		Func = function()
			assignCaptured("Dodge")
		end,
	})

	remoteBox:AddInput("RC_TemplateName", {
		Text = "Template Name",
	})

	remoteBox:AddButton({
		Text = "Save Selected As Named Template",
		Func = function()
			local entry = selectedCapture()
			local name = Options.RC_TemplateName and Options.RC_TemplateName.Value

			if not entry then
				return Logger.warn("No captured remote selected.")
			end

			if not name or #name == 0 then
				return Logger.warn("Enter a template name first.")
			end

			RemoteCapture.saveTemplate(name, entry)
			refreshRemoteDropdowns()
			Logger.notify("Saved remote template '%s' -> '%s'.", name, entry.path)
		end,
	})

	remoteBox:AddButton({
		Text = "Clear Parry Remote",
		Func = function()
			GameDataRemotes()["Parry"] = nil
			GameData.save()
			updateRemoteLabels()
		end,
	})

	remoteBox:AddButton({
		Text = "Clear Dodge Remote",
		Func = function()
			GameDataRemotes()["Dodge"] = nil
			GameData.save()
			updateRemoteLabels()
		end,
	})

	remoteBox:AddDivider()

	remoteBox:AddInput("RC_ManualPath", {
		Text = "Manual Remote Path",
	})

	remoteBox:AddDropdown("RC_ManualMethod", {
		Text = "Manual Method",
		Values = { "FireServer", "InvokeServer" },
		Default = "FireServer",
	})

	remoteBox:AddInput("RC_ManualArgs", {
		Text = "Manual Args (Lua table)",
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

local refreshAllSections

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

	local logBox = tab:AddRightGroupbox("Animation Log")

	logBox:AddToggle("AnimationLogger", {
		Text = "Animation Logger",
		Default = true,
	})

	local animLogList = logBox:AddDropdown("AnimationLogList", {
		Text = "Logged Animations",
		Values = {},
		AllowNull = true,
	})

	logBox:AddButton({
		Text = "Refresh Log",
		Func = function()
			AnimationLog.refreshDropdown(animLogList)
		end,
	})

	logBox:AddButton({
		Text = "Use Selected As Animation ID",
		Func = function()
			local value = Options.AnimationLogList and Options.AnimationLogList.Value

			if not value then
				return Logger.warn("Select a logged animation first.")
			end

			local id = tostring(value):match("^(%S+)")

			local section = BuilderSections.animation

			if section and id then
				section.loading = true
				section.timingId:SetValue(id)
				section.loading = false
				Logger.notify("Set animation id to '%s'.", id)
			end
		end,
	})

	logBox:AddButton({
		Text = "Clear Log",
		Func = function()
			AnimationLog.clear()
			AnimationLog.refreshDropdown(animLogList)
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
		animLogList = animLogList,
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
		Text = "Use Selected From Log",
		Func = function()
			local value = Options.AnimationLogList and Options.AnimationLogList.Value

			if not value then
				return Logger.warn("Select a logged animation in the Builder tab first.")
			end

			local id = tostring(value):match("^(%S+)")

			if id and Options.DiffAnimationId then
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

	local infoBox = tab:AddRightGroupbox("Info")

	infoBox:AddLabel("PlaceId: " .. tostring(placeId))
	infoBox:AddLabel("Executor: " .. ((identifyexecutor and identifyexecutor()) or "Unknown"))
	infoBox:AddLabel("Storage root: " .. ROOT_FOLDER)
	infoBox:AddLabel("Filesystem available: " .. tostring(FS_AVAILABLE and true or false))
	infoBox:AddLabel(
		"Hook available: " .. tostring(hookmetamethod and getnamecallmethod and checkcaller and true or false)
	)
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
	AnimationLog.flush()

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

	AnimationLog.dirty = true
	AnimationLog.lastFlush = 0
	pcall(AnimationLog.flush)
	pcall(GameData.save)

	pcall(Simulation.clear)
	pcall(Hitbox.clean)
	pcall(function()
		Entities.maid:clean()
	end)
	pcall(function()
		DifferenceCalculator.maid:clean()
	end)
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
	AnimationLog.load()

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

	Library.ToggleKeybind = Options.MenuKeybind

	updateRemoteLabels()
	refreshRemoteDropdowns()

	DifferenceCalculator.start()
	Entities.start()

	rootMaid:mark(runService.Heartbeat:Connect(onHeartbeat))
	rootMaid:mark(Simulation.maid)
	rootMaid:mark(Entities.maid)
	rootMaid:mark(DifferenceCalculator.maid)

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
