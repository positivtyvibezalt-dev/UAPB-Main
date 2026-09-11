local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "ShockGrenade", function(data)
		if not DungeonsTiming.number(data.Start) then
			return
		end
		local grenade = workspace:FindFirstChild(tostring(data.Start))
		if not grenade or not grenade:IsA("BasePart") then
			return
		end
		return { { when = 2, origin = grenade } }, data.Start
	end)
end
