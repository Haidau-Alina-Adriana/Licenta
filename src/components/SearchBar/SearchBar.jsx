import React, { useState } from "react";
import "../SearchBar/SearchBar.css";
import SearchIcon from '@mui/icons-material/Search';
import CloseIcon from '@mui/icons-material/Close';

function fruitInfo(name, description, image_link) {

  return (
    <div>
      <div className="container grid-one">
        <img src={require('../../images' + image_link)} alt={name} className="image-fruit"></img>
        <div className='see-more'></div>
      </div>
      <div className="container">
        <div className="name">{name}</div>
        <div className="description">{description}</div>
      </div>
    </div>
  );
}

function SearchBar({ placeholder, data }) {
  const [filteredData, setFilteredData] = useState([]);
  const [currentWord, setCurrentWord] = useState("");

  const handleChangeInput = (event) => {
    const searchedFruit = event.target.value;
    setCurrentWord(searchedFruit);
    const newFilterResult = data.filter((value) => {
      return value.name.toLowerCase().includes(searchedFruit.toLowerCase());
    });

    if (searchedFruit === "") {
      setFilteredData([]);
    } else {
      setFilteredData(newFilterResult);
    }
  }
  const clearData = () => {
    setFilteredData([]);
    setCurrentWord("");
  }

  return (
    <div className="search">
      <div className="search-input">
        <input type="text" placeholder={placeholder} value={currentWord} onChange={handleChangeInput} />
        <div className="search-icon">
          {(filteredData.length === 0) ? <SearchIcon /> : <CloseIcon id="clearBtn" onClick={clearData} />}
        </div>
      </div>
      {(filteredData.length === 0) ?
        (<div className='fruits-container'>
          {data.map((value, key) => {
            return (<div className='box-fruit' style={{ backgroundColor: value.color }}>
              {fruitInfo(value.name, value.description, value.image_link)}
            </div>);
          })}
        </div>)
        :
        (<div className='fruits-container'>
          {filteredData.map((value, key) => {
            return (<div className='box-fruit' style={{ backgroundColor: value.color }}>
              {fruitInfo(value.name, value.description, value.image_link)}
            </div>);
          })}
        </div>)
      }
    </div>
  )
}

export default SearchBar
