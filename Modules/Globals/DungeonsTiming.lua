local Action = getfenv().Action
local Latency = getfenv().Latency
local decodeNumber = getfenv().PP_SCRAMBLE_NUM
local decodeString = getfenv().PP_SCRAMBLE_STR
local players = game:GetService("Players")
local DungeonsTiming = {}

function DungeonsTiming.number(value, minimum)
	return typeof(value) == "number" and value == value and value < math.huge and value >= (minimum or 0)
end

function DungeonsTiming.count(value, minimum, maximum)
	return DungeonsTiming.number(value, minimum) and value % 1 == 0 and value <= (maximum or 256)
end

function DungeonsTiming.frame(value)
	local frame
	if typeof(value) == "Vector3" then
		frame = CFrame.new(value)
	elseif typeof(value) == "CFrame" then
		frame = value
	elseif typeof(value) == "Instance" and value.Parent then
		if value:IsA("BasePart") then
			frame = value.CFrame
		elseif value:IsA("Model") then
			frame = value:GetPivot()
		end
	end
	if not frame then
		return
	end
	for _, component in ipairs({ frame:GetComponents() }) do
		if not DungeonsTiming.number(math.abs(component)) then
			return
		end
	end
	return frame
end

function DungeonsTiming.alive(owner)
	if typeof(owner) ~= "Instance" or not owner.Parent then
		return false
	end
	local model = owner:IsA("Model") and owner or owner:FindFirstAncestorOfClass("Model")
	if not model or model == players.LocalPlayer.Character or model:GetAttribute("Died") == true then
		return false
	end
	local health = model:GetAttribute("H")
	return typeof(health) ~= "number" or health > 0
end

function DungeonsTiming.run(self, timing, name, build)
	local data = self.data
	if self.__type ~= "Effect" or self.name ~= name or typeof(data) ~= "table" then
		return
	end
	if data.End == true or data.Cancel == true or not DungeonsTiming.alive(self.owner) then
		return
	end
	if not timing.actions or timing.actions:count() ~= 1 then
		return self:notify(timing, "Dungeons modules require one Parry or Dodge action template with a calibrated hitbox.")
	end

	local template = timing.actions:stack()[1]
	local actionType = decodeString(template._type)
	local hitbox = Vector3.new(decodeNumber(template.hitbox.X), decodeNumber(template.hitbox.Y), decodeNumber(template.hitbox.Z))
	if actionType ~= "Parry" and actionType ~= "Dodge" then
		return self:notify(timing, "Dungeons action template must be Parry or Dodge.")
	end
	if not template.ihbc and (not DungeonsTiming.number(hitbox.X, 0.001) or not DungeonsTiming.number(hitbox.Y, 0.001) or not DungeonsTiming.number(hitbox.Z, 0.001)) then
		return self:notify(timing, "Dungeons action template needs a positive hitbox size.")
	end

	local events, start = build(data)
	if typeof(events) ~= "table" or #events == 0 or #events > 256 then
		return
	end
	if start ~= nil and not DungeonsTiming.number(start) then
		return
	end

	local received = os.clock()
	local age = start and math.max(0, workspace:GetServerTimeNow() - start) or 0
	local receiveDelay = start and Latency.rdelay() or 0
	local pending = {}
	for _, event in ipairs(events) do
		if not DungeonsTiming.number(event.when) or not DungeonsTiming.frame(event.origin) or not DungeonsTiming.number(event.scale or 1, 0.001) then
			return
		end
		local scaled = hitbox * (event.scale or 1)
		if not DungeonsTiming.number(scaled.X) or not DungeonsTiming.number(scaled.Y) or not DungeonsTiming.number(scaled.Z) then
			return
		end
		if event.when >= age then
			pending[#pending + 1] = event
		end
	end
	if #pending == 0 then
		return
	end

	local origins = {}
	local previous = self.hc
	local hooked = self:hook("hc", function(defender, options, ...)
		local origin = origins[options.action]
		if origin then
			if not DungeonsTiming.alive(defender.owner) then
				return false
			end
			local frame = DungeonsTiming.frame(origin)
			if not frame then
				return false
			end
			options = options:clone()
			options.part = nil
			options.cframe = frame
			options.spredict = false
		end
		return previous(defender, options, ...)
	end)
	if not hooked then
		return
	end

	for index, event in ipairs(pending) do
		local remaining = event.when - age - (os.clock() - received)
		if remaining >= 0 or event.when == 0 and start == nil then
			local action = Action.new()
			action._when = math.max(0, remaining + receiveDelay) * 1000
			action._type = actionType
			action.hitbox = hitbox * (event.scale or 1)
			action.ihbc = template.ihbc
			action.name = string.format("Dungeons %s %d", name, index)
			origins[action] = event.origin
			self:action(timing, action)
		end
	end
end

return DungeonsTiming
