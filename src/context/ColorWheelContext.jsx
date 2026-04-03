import { createContext, useContext, useState, useRef } from 'react';
import { app, actions, moods, harmonies, moodNames, harmonyNames } from '../app.ts';

const ColorWheelContext = createContext(null);

export const hslToCSS = (h, s, l) => `hsl(${h}, ${s}%, ${l}%)`;
export const getMoodName = (mood) => moodNames[mood] || 'Custom';
export const getHarmonyName = (harmony) => harmonyNames[harmony] || 'Custom';
export const getMoodByIndex = (i) => moods[i] || 'Vibrant';
export const getHarmonyByIndex = (i) => harmonies[i] || 'Complementary';
export const moodIndex = (mood) => { const i = moods.indexOf(mood); return i >= 0 ? i : 0; };
export const harmonyIndex = (harmony) => { const i = harmonies.indexOf(harmony); return i >= 0 ? i : 0; };
export const randomSeeds = () => Array.from({ length: 10 }, () => Math.floor(Math.random() * 101));

export function ColorWheelProvider({ children }) {
  const [h, setH] = useState(() => app.Init());
  const hRef = useRef(h);
  hRef.current = h;

  const model = app.Present(h);

  const dispatch = (action) => {
    const newH = app.Dispatch(hRef.current, action);
    hRef.current = newH;
    setH(newH);
  };

  const preview = (action) => {
    const newH = app.Preview(hRef.current, action);
    hRef.current = newH;
    setH(newH);
  };

  const commitFrom = (baseline) => {
    const newH = app.CommitFrom(hRef.current, baseline);
    hRef.current = newH;
    setH(newH);
  };

  const getRawPresent = () => app.Present(hRef.current);

  const undo = () => { const newH = app.Undo(hRef.current); hRef.current = newH; setH(newH); };
  const redo = () => { const newH = app.Redo(hRef.current); hRef.current = newH; setH(newH); };
  const canUndo = app.CanUndo(h);
  const canRedo = app.CanRedo(h);

  return (
    <ColorWheelContext.Provider value={{
      model, dispatch, preview, commitFrom, getRawPresent,
      undo, redo, canUndo, canRedo, actions,
    }}>
      {children}
    </ColorWheelContext.Provider>
  );
}

export function useColorWheel() {
  const context = useContext(ColorWheelContext);
  if (!context) throw new Error('useColorWheel must be used within a ColorWheelProvider');
  return context;
}
