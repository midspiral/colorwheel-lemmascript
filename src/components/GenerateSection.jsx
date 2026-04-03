import { useState } from 'react';
import { useColorWheel, getMoodName, getHarmonyName, getMoodByIndex, getHarmonyByIndex, moodIndex, harmonyIndex, randomSeeds } from '../context/ColorWheelContext';

export function GenerateSection() {
  const { model, dispatch, actions } = useColorWheel();

  const [selectedMood, setSelectedMood] = useState(moodIndex(model.mood));
  const [selectedHarmony, setSelectedHarmony] = useState(harmonyIndex(model.harmony));

  const isShift =
    selectedMood === moodIndex(model.mood) &&
    selectedHarmony === harmonyIndex(model.harmony);

  const handleGenerateOrShift = () => {
    dispatch(actions.GeneratePalette(model.baseHue, getMoodByIndex(selectedMood), getHarmonyByIndex(selectedHarmony), randomSeeds()));
  };

  const handleRegenerate = () => {
    dispatch(actions.RandomizeBaseHue(Math.floor(Math.random() * 360), randomSeeds()));
  };

  return (
    <section className="section">
      <h3>Generate</h3>
      <div className="field">
        <label>Mood</label>
        <select value={selectedMood} onChange={(e) => setSelectedMood(Number(e.target.value))}>
          <option value={0}>Vibrant</option>
          <option value={1}>Soft/Muted</option>
          <option value={2}>Pastel</option>
          <option value={3}>Deep/Jewel</option>
          <option value={4}>Earth</option>
          <option value={5}>Neon</option>
        </select>
      </div>
      <div className="field">
        <label>Harmony</label>
        <select value={selectedHarmony} onChange={(e) => setSelectedHarmony(Number(e.target.value))}>
          <option value={0}>Complementary</option>
          <option value={1}>Triadic</option>
          <option value={2}>Analogous</option>
          <option value={3}>Split-Complement</option>
          <option value={4}>Square</option>
        </select>
      </div>
      <div className="button-row">
        <button className="btn btn-primary" onClick={handleGenerateOrShift}>
          {isShift ? 'Shift' : 'Generate'}
        </button>
        <button className="btn" onClick={handleRegenerate}>Randomize</button>
      </div>
      <div className="status-text">
        {getMoodName(model.mood)} + {getHarmonyName(model.harmony)}
      </div>
    </section>
  );
}
