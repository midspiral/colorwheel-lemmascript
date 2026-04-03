import { ColorWheelProvider, useColorWheel } from './context/ColorWheelContext';
import {
  GenerateSection,
  AdjustSection,
  Palette,
  ContrastSection,
  HistoryControls,
} from './components';
import './App.css';

function Dashboard() {
  const { model } = useColorWheel();

  return (
    <div className="dashboard">
      <div className="panel panel-controls">
        <div className="panel-header">
          <h1>ColorWheel</h1>
          <span className="subtitle">Verified Palette Generator</span>
        </div>
        <GenerateSection />
        <AdjustSection />
        <HistoryControls />
      </div>
      <div className="panel panel-view">
        <Palette contrastFg={model.contrastPair.fg} contrastBg={model.contrastPair.bg} />
        <ContrastSection />
        <div className="footer-text">
          All state transitions verified with{' '}
          <a href="https://github.com/midspiral/LemmaScript" target="_blank" rel="noopener">
            LemmaScript
          </a>
        </div>
      </div>
    </div>
  );
}

export default function App() {
  return (
    <ColorWheelProvider>
      <div className="app">
        <Dashboard />
      </div>
    </ColorWheelProvider>
  );
}
