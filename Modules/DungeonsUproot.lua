local DungeonsTiming = getfenv().DungeonsTiming
local offsets = {
	Vector3.new(-0.00000095367431640625, 0, 6),
	Vector3.new(0.324981689453125, -0.009613037109375, 18.39996337890625),
	Vector3.new(-0.00000095367431640625, 0, 31.199981689453125),
	Vector3.new(-0.00000095367431640625, 0, 44.699981689453125),
	Vector3.new(-0.00000095367431640625, 0, 58.79998779296875),
	Vector3.new(-0.00000095367431640625, 0, 73.5),
}

return function(self, timing)
	return DungeonsTiming.run(self, timing, "Uproot", function(data)
		if not DungeonsTiming.alive(data.Owner) or not DungeonsTiming.number(data.Start) or not DungeonsTiming.number(data.DelayPerHitbox) then
			return
		end
		local center = DungeonsTiming.frame(data.Target)
		if not center then
			return
		end
		center = center * CFrame.Angles(0, math.pi, 0)
		local events = {}
		for index, offset in ipairs(offsets) do
			events[index] = { when = (index - 1) * data.DelayPerHitbox, origin = center * CFrame.new(offset) }
		end
		return events, data.Start
	end)
end
