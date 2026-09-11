local DungeonsTiming = getfenv().DungeonsTiming
local ringCounts = { 12, 22, 24 }

return function(self, timing)
	return DungeonsTiming.run(self, timing, "FrostGolem360Ice", function(data)
		if not DungeonsTiming.alive(data.Owner) or not DungeonsTiming.number(data.Start) or not DungeonsTiming.count(data.Rounds, 1, 3) or not DungeonsTiming.number(data.HitDelay) then
			return
		end
		local center = DungeonsTiming.frame(data.Target)
		if not center then
			return
		end
		local events = {}
		for ring = 0, data.Rounds - 1 do
			local count = ringCounts[ring + 1]
			for index = 1, count do
				events[#events + 1] = {
					when = ring * data.HitDelay,
					origin = center * CFrame.Angles(0, 2 * math.pi * index / count, 0) * CFrame.new(0, 0, -11 - ring * 13),
				}
			end
		end
		return events, data.Start
	end)
end
