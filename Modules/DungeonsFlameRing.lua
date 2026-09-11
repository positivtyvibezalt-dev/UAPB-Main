local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "FlameRing", function(data)
		if not DungeonsTiming.alive(data.Target) or not DungeonsTiming.number(data.Start) then
			return
		end
		return { { when = 0.65, origin = data.Position } }, data.Start
	end)
end
