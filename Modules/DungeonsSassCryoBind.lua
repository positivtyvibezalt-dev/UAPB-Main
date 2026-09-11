local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "SassCryoBind", function(data)
		if not DungeonsTiming.alive(data.Owner) or not DungeonsTiming.number(data.Start) or not DungeonsTiming.number(data.Delay) or typeof(data.Targets) ~= "table" then
			return
		end
		if not DungeonsTiming.count(#data.Targets, 1) then
			return
		end
		local events = {}
		for index, origin in ipairs(data.Targets) do
			events[index] = { when = data.Delay, origin = origin }
		end
		return events, data.Start
	end)
end
